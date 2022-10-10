open Globals
open Gen
open VarGen

open Cpure
open Term

open Com
open Aentry

module CF = Cformula

type t = {
    form : CF.t;
    inv_arith: Cpure.t;
}

let string_of (e: t)=
    "f = " ^ ((CF.string_of) e.form) ^ "\n" ^
        "inv_arith = " ^ ((Cpure.string_of) e.inv_arith) ^ "\n"

  let string_of_short (e: t)=
    "f = " ^ ((CF.string_of) e.form) ^ "\n"

  let mk f inv= {
      form = f;
      inv_arith = inv;
  }

  let eval e=
    Out.UNKNOWN


class sl_entry init= object
  inherit [t] aentry init as super

  method string_of () = string_of (super # get_e ())
  method string_of_short () = string_of_short (super # get_e ())
  method eval () = eval (super # get_e ())


end;;
