signature ORD_KEY =
sig
  eqtype key
  type value
  type asser

  val compose     : asser -> asser -> asser
  val unitAssr    : asser
end

(* Signature of the type environment used by type-checker module *)
signature TYPE_ENVIRONMENT =
sig 
  structure Key : ORD_KEY
  type env

  val find        : env -> Key.key -> Key.value option
  val extend      : env -> Key.key -> Key.value -> env 
  val extendl     : env -> (Key.key * Key.value) list -> env 
  val extendAssr  : env -> Key.asser -> env 
  val getMap      : env -> Key.key list
  val getTEnv     : env -> (Key.key * Key.value) list
  val getAssr     : env -> Key.asser 
  val empty       : env 

end

functor TypeEnv (Key : ORD_KEY) : TYPE_ENVIRONMENT = 
struct 
  structure Key = Key

  local 
      open Lst
      open Tpl
  in 

    type env = ((Key.key * Key.value) list * Key.asser)

    fun find (e,_) k = Lst.assoc k e     

    fun ext (k,v) e =
      case Lst.assoc k e of 
        SOME _ => (print ("\nWarning: Name already in the domain of E!\n\n");e) 
      | NONE   => (k,v)::e

    fun extend (e,a) k v = (ext (k,v) e, a) 

    fun extendl (e,a) kvl = (foldl ext e kvl, a)

    fun extendAssr (e,a) assr = (e, Key.compose a assr)

    fun getMap  (e,_) = fsl e

    fun getTEnv (e,_) = e 

    fun getAssr (_,a) = a

    val empty = ([] , Key.unitAssr)

  end
end
