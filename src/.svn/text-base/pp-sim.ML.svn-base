(* uses src/missing,
        src/pp,
        src/pp-psi,
        src/simulator
*)

(* pretty printing typed output action *)

functor PPStrongAction
    (A : 
    sig
      structure PP     : PRETTY_PRINTER
      structure Act    : PSI_STRONG_ACTION
      structure PPInst : PSI_INSTANCE_PRETTY_PRINTER
      sharing Act.Inst = PPInst.Inst
    end):
    sig
      structure PP     : PRETTY_PRINTER
      structure Act    : PSI_STRONG_ACTION
      structure PPInst : PSI_INSTANCE_PRETTY_PRINTER
      sharing Act.Inst = PPInst.Inst

      val ppAction : Act.action -> PP.document
    end =
struct

  open A open PP open Missing
  structure PPA = PrettyPrinterAux(PP)
  open PPA
  structure EPInst = EscapedPsiInstancePrettyPrinter(struct
    structure PP = PP
    structure PPInst = PPInst
  end)
  open EPInst

  fun ppAction alpha =
    case alpha of
         Act.Tau => text "tau"
       | Act.Output (y,avec,m) =>

        let 
            fun printNameTy (na,typ') = 
                n na </sp/> text ":" </sp/> typ typ'
        in
           t y </join/>
                    (if not (null avec)
                        then
                                     text "(\\"
                            </join/> filledCommaSep (map printNameTy avec)
                            </join/> text ")"
                        else
                            text " ")
                  </join/> t m
        end
       | Act.Input (z,x) =>
           t z </join/> text "(" </join/> n x </join/> text ")"

end;
