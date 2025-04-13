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

let db_to_int : Lir.db -> int =
        let rec aux acc = function
                | Lir.H _ -> acc
                | Lir.U (_, _, _, n) -> aux (acc + 1) n
        in
        aux 0

let rec dump_lir : Lir.tm -> unit = function
        | Lir.Var (_, _, n) ->
                        printf "$%d" (db_to_int n)
        | Lir.Lam (_, ta, _, m) ->
                        printf "(\\"; dump_typ ta; printf ". "; dump_lir m; printf ")"
        | Lir.App (_, _, _, f, a) ->
                        printf "("; dump_lir f; printf " "; dump_lir a; printf ")"
        | Lir.Unit _ ->
                        printf "()"
        | Lir.Let (_, _, _, v, e) ->
                        printf "(let "; dump_lir v; printf " in "; dump_lir e; printf ")"
        | Lir.Pair (_, _, _, l, r) ->
                        printf "("; dump_lir l; printf ", "; dump_lir r; printf ")"
        | Lir.Fst (_, _, _, p) ->
                        printf "(fst "; dump_lir p; printf ")"
        | Lir.Snd (_, _, _, p) ->
                        printf "(snd "; dump_lir p; printf ")"
        | Lir.Inl (_, _, _, p) ->
                        printf "(inl "; dump_lir p; printf ")"
        | Lir.Inr (_, _, _, p) ->
                        printf "(inr "; dump_lir p; printf ")"
        | Lir.Case (_, a, b, _, s, p, q) ->
                        printf "(case "; dump_lir s;
                        printf " of inl "; dump_typ a; printf ". "; dump_lir p;
                        printf " | inr "; dump_typ b; printf ". "; dump_lir q;
                        printf ")"

let () =
        let lexbuf = Lexing.from_channel stdin in
        let ast = Parser.prog Lexer.read lexbuf in
        match Ela.elab_infer Lir.Nil (fun _ -> None) ast with
        | None -> failwith "Semantic checking failed due to invalid program or missing type information"
        | Some (Ela.Ev (t, lir)) ->
                        dump_lir lir;
                        printf "\n  : ";
                        dump_typ t;
                        printf "\n"

