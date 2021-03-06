(* uses  src/missing
         src/simulator
*)

signature WEAK_SYMBOLIC_TRANSITION =
sig
  structure Psi : PSI
  structure Constraint : SYMBOLIC_TRANSITION_CONSTRAINT
  sharing Psi.Inst = Constraint.Inst

  datatype weak_action
    = Silent
    | Tau
    (* type introduction *)
    | Output of Psi.Inst.term * (Psi.Inst.name * Psi.Inst.ty) list * Psi.Inst.term
    | Input  of Psi.Inst.term * Psi.Inst.name

  type weak_transition
    = Psi.Inst.assertion
        * Psi.psi * weak_action * Constraint.constraint * Psi.psi

end;



functor WeakSymbolicTransition(A :
    sig
      structure Psi        : PSI
      structure Constraint : SYMBOLIC_TRANSITION_CONSTRAINT
      sharing Psi.Inst = Constraint.Inst
    end): WEAK_SYMBOLIC_TRANSITION =
struct
  open A

  datatype weak_action
    = Silent
    | Tau
    (* type introduction *)
    | Output of Psi.Inst.term * (Psi.Inst.name * Psi.Inst.ty) list * Psi.Inst.term
    | Input  of Psi.Inst.term * Psi.Inst.name

  type weak_transition
    = Psi.Inst.assertion
        * Psi.psi * weak_action * Constraint.constraint * Psi.psi
end;



signature WEAK_SYMBOLIC_PSI_SIMULATOR =
sig
  structure Sim : SYMBOLIC_PSI_SIMULATOR
  structure Tr  : WEAK_SYMBOLIC_TRANSITION

  (**
   * Compute all weak transitions
   *)
  val reduce
    : Sim.ClEnv.env -> Sim.Psi.Inst.assertion -> Sim.Psi.psi
    -> Tr.weak_transition list

  (**
   * Compute all the silent weak transitions
   *)
  val silent
    : Sim.ClEnv.env -> Sim.Psi.Inst.assertion -> Sim.Psi.psi
    -> Tr.weak_transition list

  (**
   * Compute all the weak transitions with an action
   *)
  val action
    : Sim.ClEnv.env -> Sim.Psi.Inst.assertion -> Sim.Psi.psi
    -> Tr.weak_transition list

  sharing Sim.Psi = Tr.Psi
end;


functor WeakSymbolicPsiSimulator(SI: SYMBOLIC_PSI)
    : WEAK_SYMBOLIC_PSI_SIMULATOR =
struct
  structure Sim = SymbolicPsiSimulator(SI)
  structure Tr  = WeakSymbolicTransition(struct
    structure Psi        = SI.Psi
    structure Constraint = SI.Constraint
  end)

  open Missing

  fun mapconcat f l = List.concat (map f l)

  fun translateAction  Sim.Tr.Act.Tau         = Tr.Tau
    | translateAction (Sim.Tr.Act.Output out) = Tr.Output out
    | translateAction (Sim.Tr.Act.Input  inp) = Tr.Input  inp

  fun silent1 e psi p = [(psi, p, Tr.Silent, [], p)]

  and silent2 e psi p =
  let
    val taus = Sim.reduce e psi p |>
        List.filter (fn (psi,p,Sim.Tr.Act.Tau,c,p'') => true | _ => false)
  in
    taus |> mapconcat
        (fn (psi,p  ,_,c ,p'') => silent e psi p'' |> map
        (fn (psi,p'',_,c',p' ) => (psi, p, Tr.Silent, c @ c', p')))
  end

  and silent e psi p =
    silent1 e psi p @ silent2 e psi p

  and action e psi p =
    (silent e psi p) |> (mapconcat
        (fn (psi,p,_,c,p'')         => (Sim.reduce e psi p'') |> mapconcat
        (fn (psi,p'',alpha,c',p''') => (silent e psi (p''')) |> map
        (fn (psi,p''',_,c'',p')     =>
            (psi,p,translateAction alpha, c @ c' @ c'',p')))))


  and reduce e psi p = silent e psi p @ action e psi p

end;

