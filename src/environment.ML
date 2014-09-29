signature ORD_KEY =
sig
  structure Assr: NOMINAL
  structure Type: NOMINAL

  sharing type Assr.atom = Type.atom

  val compose     : Assr.data -> Assr.data -> Assr.data
  val unitAssr    : Assr.data

end

(* Signature of the type environment used by type-checker module *)
signature TYPE_ENVIRONMENT =
sig 

  type env
  type name
  type typ 
  type asser

  val find        : env -> name -> typ option
  val extend      : env -> name -> typ -> env 
  val extendl     : env -> (name * typ) list -> env 
  val extendAssr  : env -> asser -> env 
  val getMap      : env -> name list
  val getTEnv     : env -> (name * typ) list
  val getAssr     : env -> asser 
  val empty       : env 

end

functor TypeEnv (Key : ORD_KEY) : TYPE_ENVIRONMENT = 
struct 

  local 
      open Lst
      open Tpl
  in 
    type name  = Key.Assr.atom
    type typ   = Key.Type.data
    type asser = Key.Assr.data 
    type env   = ((name * typ) list * asser)

    fun find (e,_) k = Lst.assoc k e     

    fun ext (k,v) e =
      case Lst.assoc k e of 
        SOME _ => (print ("\nWarning: Name already in the domain of E!\n\n"); e) 
      | NONE   => let val nameInTyInE = intersection (Key.Type.support v) (fsl e)
                  in  
                    if (nameInTyInE <> (Key.Type.support v)) then 
                    (print ("\nErr: Names in type not already in the domain of E!\n\n"); e) 
                    else (k,v)::e
                  end

    fun extend (e,a) k v = (ext (k,v) e, a) 

    fun extendl (e,a) kvs = (foldl ext e kvs, a)

    fun extendAssr (e,a) assr = 
      let val nameInAssrInE = intersection (Key.Assr.support assr) (fsl e) 
      in 
        if (nameInAssrInE <> (Key.Assr.support assr)) then
          (print ("\nErr: Names in assertion not already in the domain of E!\n\n"); (e,a)) 
        else (e, Key.compose a assr)
      end 

    fun getMap  (e,_) = fsl e

    fun getTEnv (e,_) = e 

    fun getAssr (_,a) = a

    val empty = ([] , Key.unitAssr)

  end
end
