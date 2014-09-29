(*
* TODO: finish substitution module
*)
signature SUBSTITUTION_SEQUENCE =
sig
  type substseq
  type dom
  type ran

  val dom     : substseq -> dom list
  val compose : substseq * substseq -> substseq
end;


