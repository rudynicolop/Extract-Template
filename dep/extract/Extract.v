From Coq Require extraction.Extraction.
Require Import Coq.extraction.ExtrOcamlBasic.

(** Extraction of [nat] to [Zarith]'s [Z.t]. *)
Extract Inductive nat => "Z.t" ["Z.zero" "Z.succ"].

Extract Inlined Constant plus => "Z.add".

Require MyVector.Victor.

Separate Extraction MyVector.Victor.
