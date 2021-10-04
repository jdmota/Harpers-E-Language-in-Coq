Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PFPL Require Import Theorems_Eval.

(* From https://softwarefoundations.cis.upenn.edu/lf-current/Extraction.html *)

Require Coq.extraction.Extraction.
Extraction Language OCaml.

Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n -> if n=0 then zero () else succ (n-1))".

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Extraction "eval.ml" eval_big.
