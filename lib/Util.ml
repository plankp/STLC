(**
   A bunch of routines for converting between Coq and OCaml types
 *)

let ml_to_coq_str : string -> char list =
        fun s -> s |> String.to_seq |> List.of_seq

let coq_to_ml_str : char list -> string =
        fun s -> s |> List.to_seq |> String.of_seq

