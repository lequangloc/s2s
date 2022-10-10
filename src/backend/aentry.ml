open Globals
open Gen
open VarGen

class virtual ['a] aentry init = object
  val m_e : 'a = init
  method virtual string_of : unit -> ident
  method virtual string_of_short : unit -> ident
  method virtual eval : unit -> Out.outcome

  method get_e () = (m_e:'a)

end;;
