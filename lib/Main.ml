open Printf

let rec dump_typ : Typ.tp -> unit = function
        | Typ.TArr (a, b) ->
                        printf "("; dump_typ a; printf " -> "; dump_typ b; printf ")"
        | Typ.TUnit ->
                        printf "()"
        | Typ.TPair (a, b) ->
                        printf "("; dump_typ a; printf " * "; dump_typ b; printf ")"
        | Typ.TInj (a, b) ->
                        printf "("; dump_typ a; printf " + "; dump_typ b; printf ")"

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

let rec dump_lir : string list -> Lir.tm -> unit = fun ctx -> function
        | Lir.Var (_, _, n) ->
                        printf "%s" (db_lookup ctx n)
        | Lir.Lam (_, ta, _, m) ->
                        let x = mk_fresh ctx in
                        printf "\\(%s : " x; dump_typ ta; printf "). "; dump_lir (x :: ctx) m
        | Lir.App (_, _, _, f, a) ->
                        printf "("; dump_lir ctx f; printf " "; dump_lir ctx a; printf ")"
        | Lir.Unit _ ->
                        printf "()"
        | Lir.Let (_, _, _, v, e) ->
                        let x = mk_fresh ctx in
                        printf "(let %s = " x; dump_lir ctx v; printf " in "; dump_lir (x :: ctx) e; printf ")"
        | Lir.Pair (_, _, _, l, r) ->
                        printf "("; dump_lir ctx l; printf ", "; dump_lir ctx r; printf ")"
        | Lir.Fst (_, _, _, p) ->
                        printf "(fst "; dump_lir ctx p; printf ")"
        | Lir.Snd (_, _, _, p) ->
                        printf "(snd "; dump_lir ctx p; printf ")"
        | Lir.Inl (_, tl, tr, p) ->
                        printf "(inl "; dump_lir ctx p; printf " : "; dump_typ (Typ.TInj (tl, tr));
                        printf ")"
        | Lir.Inr (_, tl, tr, p) ->
                        printf "(inr "; dump_lir ctx p; printf " : "; dump_typ (Typ.TInj (tl, tr));
                        printf ")"
        | Lir.Case (_, _, _, _, s, p, q) ->
                        let x = mk_fresh ctx in
                        let y = mk_fresh ctx in
                        printf "(case "; dump_lir ctx s;
                        printf " of inl %s. " x; dump_lir (x :: ctx) p;
                        printf " | inr %s. " y; dump_lir (y :: ctx) q;
                        printf ")"


let () =
        let lexbuf = Lexing.from_channel stdin in
        let ast = Parser.prog Lexer.read lexbuf in
        match Ela.elab_infer Lir.Nil (fun _ -> None) ast with
        | None -> failwith "Semantic checking failed due to invalid program or missing type information"
        | Some (Ela.Ev (t, lir)) ->
                        dump_lir [] lir;
                        printf "\n  : ";
                        dump_typ t;
                        printf "\n"

