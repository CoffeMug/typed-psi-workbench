(* uses src/missing,
        src/parser,
        src/psi-parsing,
        src/pp,
        src/psi
*)

signature PSI_PRETTY_PRINTER =
sig
  structure PP  : PRETTY_PRINTER
  structure Psi : PSI

  val n : Psi.Inst.name      -> PP.document
  val t : Psi.Inst.term      -> PP.document
  val a : Psi.Inst.assertion -> PP.document
  val c : Psi.Inst.condition -> PP.document

  (* pretty printing types *)
  val typ: Psi.Inst.ty   -> PP.document

  val ppAgent : Psi.psi -> PP.document
end;


signature PSI_INSTANCE_PRETTY_PRINTER =
sig
  structure Inst : PSI_INSTANCE

  val printN  : Inst.name      -> string
  val printT  : Inst.term      -> string
  val printC  : Inst.condition -> string
  val printA  : Inst.assertion -> string
  
  (* pretty printing types *)
  val printTy : Inst.ty  -> string

  val var     : ((Inst.name * Inst.ty) -> Inst.term) option
end;



functor EscapedPsiInstancePrettyPrinter
    (A: sig
      structure PP     : PRETTY_PRINTER
      structure PPInst : PSI_INSTANCE_PRETTY_PRINTER
    end) :
sig
  structure PPInst : PSI_INSTANCE_PRETTY_PRINTER
  structure PP     : PRETTY_PRINTER

  val n  : PPInst.Inst.name      -> PP.document
  val t  : PPInst.Inst.term      -> PP.document
  val c  : PPInst.Inst.condition -> PP.document
  val a  : PPInst.Inst.assertion -> PP.document

  (* Todo : not sure about this, check it with Johannes or Ramunas *) 
  val typ : PPInst.Inst.ty -> PP.document

end =
struct
  open A
  open Missing
  open PP
  open PPInst
  structure StringParser = Parser(StringStream)
  structure B = PsiParserBase(StringParser)

  local open StringParser in
  fun escape s =
  let
    val str = StringStream.make s
  in
    (* check if "s" is an identifier *)
    case parse (B.identifier >>= eof) str of
         RIGHT _ => s           (* if yes return unmodified *)
       | LEFT _  => escape' s   (* if no escape *)
  end
  and escape' s =
    "\"" ^ (String.concat $
        map (fn c => if c = #"\"" then "\\\"" else String.str c ) $
            String.explode s) ^ "\""
  end

  fun liftEscape f = text o escape o f

  (* The lifted functions *)
  val t  = liftEscape printT
  val n  = liftEscape printN
  val c  = liftEscape printC
  val a  = liftEscape printA
  val typ = liftEscape printTy

end;



functor PrettyPrintPsi
(A: sig
  structure PP     : PRETTY_PRINTER
  structure PPInst : PSI_INSTANCE_PRETTY_PRINTER
  structure Psi    : PSI
  sharing Psi.Inst = PPInst.Inst
end) : PSI_PRETTY_PRINTER =
struct
  open A
  structure PP  = PP
  structure Psi = Psi
  structure PPA = PrettyPrinterAux(PP)
  structure EPInst = EscapedPsiInstancePrettyPrinter(
  struct
    structure PP = PP
    structure PPInst = PPInst
  end)
  open EPInst
local
  open Missing
  open Psi
  open PP
  open PPA
  open PPInst
in


  fun collapseNew' (Restriction (a,t,p)) avec = collapseNew' p ((a,t) :: avec)
    | collapseNew' p avec = (avec, p)

  fun collapseNew p = collapseNew' p []

  fun nestIndent d = nest 2 d

  fun enclose a doc b =
    text a </join/> doc </join/> text b

  fun isSingleInput (Input (_, [x], x', _)) =
    maybe false (fn v => Psi.Inst.Term.eqData (v x, x')) var
    | isSingleInput _ = false

  (* Auxilary function used for printing typed names *)
  fun printNameTy (na,typ') = 
                n na </sp/> text ":" </sp/> typ typ'

  fun dot (a,p) =
    a </join/>
        (case p of
              Nil => empty
            | _ => text "." </join/>
                    nestIndent (line </join/> (print' p)))

  and print' Nil = text "0"
    | print' (Output (m, n, p)) =
        group $
        text "'" </join/> t m </join/>
            (enclose "<" (t n) ">") </dot/> p

    | print' (inp as Input (m, xvec, nn, p)) =
        group $
        t m  </join/>
            (if isSingleInput inp
                then enclose "(" (commaSep (map printNameTy xvec)) ")"
                else enclose "(\\" (commaSep (map printNameTy xvec)) ")"
                </join/> t nn )
                </dot/> p
    
    | print' (Case cs) =
        let
          fun printCaseClause (cond,p) =
            c cond </sp/> text ":" </sp/> (print' p)
        in
        group $
            text "case" </join/>
                nestIndent
                    (line </join/>
                    (sep (text " " </join/>text "[]" </join/> line)
                         (map printCaseClause cs) ))
                </join/> line
        end
    | print' (proc as (Restriction _)) =
        let
          val (avec,p) = collapseNew proc
        in
          enclose "(new " (commaSep (map printNameTy avec)) ")"
            </join/>
                group (text "(" </join/> nestIndent
                                    (line </join/> print' p)
                                        </join/> line </join/>
                        text ")")
        end
    | print' (Parallel (p, q)) =
        group $ text "(" </join/> print' p </join/> text ")"
                </sp/> text "|" </join/>
                    (nestIndent $
                        line </join/>
                        text "(" </join/> print' q </join/> text ")")
    | print' (Replication p) =
        text "!(" </join/> print' p </join/> text ")"
    | print' (Assertion assr) =
        text "(|" </join/> a assr </join/> text "|)"
    | print' (Invocation (a, mvec)) =
        t a </join/> text "<" </join/> commaSep (map t mvec)
            </join/> text ">"

  fun ppAgent p = print' p

end
end;

functor PPClause(A : sig
                        structure PP    : PRETTY_PRINTER
                        structure Cl    : PSI_CLAUSE
                        structure PPPsi : PSI_PRETTY_PRINTER
                        sharing PP = PPPsi.PP
                        sharing Cl.Psi = PPPsi.Psi
                      end):
                      sig
                        structure PP    : PRETTY_PRINTER
                        structure Cl    : PSI_CLAUSE
                        structure PPPsi : PSI_PRETTY_PRINTER
                        sharing PP = PPPsi.PP
                        sharing Cl.Psi = PPPsi.Psi

                        val ppClause        : Cl.clause -> PP.document
                        val ppClauseFormals : Cl.clause -> PP.document
                      end =
struct
  open A open PP open Missing
  structure PPA = PrettyPrinterAux(PP) open PPA

  (* Auxilary function used for printing typed names *)
  fun printNameTy (na,typ') = 
                PPPsi.n na </sp/> text ":" </sp/> PPPsi.typ typ'

  (*
    A(x1:t1, x2:t2,..)
  *)
  fun ppClauseFormals (a,xvec,p) =
    (PPPsi.t a) </join/> text "("
                </join/> filledCommaSep (map printNameTy xvec)
                </join/> text ")"


  (*
    A(x:t1, x2:t2,..) <= P
  *)
  fun ppClause (a,xvec,p) =
        ppClauseFormals (a,xvec,p)
        </sp/> text "<="
            </join/> group (nest 2 (line </join/> PPPsi.ppAgent p))


end;

