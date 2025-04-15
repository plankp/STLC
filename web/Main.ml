open Js_of_ocaml
open Stlclib
open Printf

let rec dump_typ : Buffer.t -> Typ.tp -> unit = fun buf -> function
        | Typ.TArr (a, b) ->
                        bprintf buf "(%a -> %a)" dump_typ a dump_typ b
        | Typ.TUnit ->
                        bprintf buf "()"
        | Typ.TPair (a, b) ->
                        bprintf buf "(%a * %a)" dump_typ a dump_typ b
        | Typ.TInj (a, b) ->
                        bprintf buf "(%a + %a)" dump_typ a dump_typ b

let mk_fresh : string list -> string =
        fun live ->
                let rec aux acc = function
                        | [] -> sprintf "x%d" acc
                        | x :: xs ->
                                        if x = sprintf "x%d" acc then aux (acc + 1) live
                                                                 else aux acc xs
                in
                aux 0 live

let rec db_lookup : 'a list -> Lir.db -> 'a =
        fun xs d -> match (xs, d) with
                    | (x :: _, Lir.H _) -> x
                    | (_ :: xs, Lir.U (_, _, _, n)) -> db_lookup xs n
                    | _ -> failwith "INVALID CONTEXT"

let rec dump_lir : Buffer.t -> (string list * Lir.tm) -> unit = fun buf (ctx, m) -> match m with
        | Lir.Var (_, _, n) ->
                        bprintf buf "%s" (db_lookup ctx n)
        | Lir.Lam (_, ta, _, m) ->
                        let x = mk_fresh ctx in
                        bprintf buf "\\(%s : %a). %a" x dump_typ ta dump_lir (x :: ctx, m)
        | Lir.App (_, _, _, f, a) ->
                        bprintf buf "(%a %a)" dump_lir (ctx, f) dump_lir (ctx, a)
        | Lir.Unit _ ->
                        bprintf buf "()"
        | Lir.Let (_, _, _, v, e) ->
                        let x = mk_fresh ctx in
                        bprintf buf "(let %s = %a in %a)" x dump_lir (ctx, v) dump_lir (x :: ctx, e)
        | Lir.Pair (_, _, _, l, r) ->
                        bprintf buf "(%a, %a)" dump_lir (ctx, l) dump_lir (ctx, r)
        | Lir.Fst (_, _, _, p) ->
                        bprintf buf "(fst %a)" dump_lir (ctx, p)
        | Lir.Snd (_, _, _, p) ->
                        bprintf buf "(snd %a)" dump_lir (ctx, p)
        | Lir.Inl (_, tl, tr, p) ->
                        bprintf buf "((inl %a) : %a)" dump_lir (ctx, p) dump_typ (Typ.TInj (tl, tr))
        | Lir.Inr (_, tl, tr, p) ->
                        bprintf buf "((inr %a) : %a)" dump_lir (ctx, p) dump_typ (Typ.TInj (tl, tr))
        | Lir.Case (_, _, _, _, s, p, q) ->
                        let x = mk_fresh ctx in
                        let y = mk_fresh ctx in
                        bprintf buf "(case %a of inl %s. %a | inr %s. %a)" dump_lir (ctx, s) x dump_lir (x :: ctx, p) y dump_lir (y :: ctx, q)

let infer_ : string -> Lir.tm Ela.hidden Ela.elabres = fun c ->
        c |> Lexing.from_string
          |> Parser.prog Lexer.read
          |> Ela.elab_infer Lir.Nil (fun _ -> None)

let to_err_msg_ : Lir.tm Ela.hidden Ela.elabres -> string = function
        | Ela.Ok _ -> "Success"
        | Ela.UndefName n -> sprintf "Name %s is not in scope" (Util.coq_to_ml_str n)
        | Ela.NeedAnnot -> "Type annotation is needed"
        | Ela.WrongType -> "Type mismatch"

let dump_ir_ : Lir.tm Ela.hidden Ela.elabres -> string = function
        | Ela.Ok (Ev (_, lir)) ->
                        let buf = Buffer.create 128 in
                        dump_lir buf ([], lir);
                        Buffer.contents buf
        | _ -> ""

let _ =
        Js.export "stlcLib"
        (object%js (_self)
                val name = "CamlWorld" [@@read]

                method infer = infer_
                method toErrMsg = to_err_msg_
                method dumpIR = dump_ir_
        end)

