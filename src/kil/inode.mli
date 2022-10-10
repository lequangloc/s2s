open Globals
open Gen.Basic
open VarGen
open Exc.GTable

type data_decl = { 
  data_name : ident;
  data_fields : (typed_ident * loc) list;
  data_parent_name : ident;
  data_pos : loc;
  data_is_template: bool }

type t = data_decl


val string_of: t -> string

val mk : ident -> (typed_ident * loc) list -> ident -> loc -> bool -> t

val gen_field_ann: typ -> string

val get_field_pos : (typed_ident * loc) -> loc

val get_field_name : (typed_ident * loc) -> ident

val get_field_typ : (typed_ident * loc) -> typ

val look_up_data_def : t list -> Globals.ident -> t

val look_up_types_containing_field : t list -> Globals.ident -> Globals.ident list

val is_not_data_type_identifier : t list -> Globals.ident -> bool

val get_type_of_field_seq : t list -> Globals.typ -> Globals.ident list -> Globals.typ

val look_up_all_fields : t list -> t -> (Globals.typed_ident * VarGen.loc ) list

val look_up_all_fields_cname : t list -> ident -> (Globals.typed_ident * VarGen.loc) list

val compute_field_seq_offset : t list -> Globals.ident -> Globals.ident list -> int

val compute_typ_size : data_decl list -> Globals.typ -> int

val build_hierarchy :  t list -> unit

val exists_path : ident -> ident -> bool

val sub_type2 : typ -> typ -> bool

val sub_type : typ -> typ -> bool

val compatible_types : typ -> typ -> bool

val inbuilt_build_exc_hierarchy: unit -> unit

val build_exc_hierarchy : bool -> t list -> unit
