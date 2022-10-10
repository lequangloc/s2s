open Globals

module CP = Cpure

val arith_abduce : ((CP.t * CP.t) list) -> CP.t -> CP.t -> bool * ((CP.t * CP.t) list)

val arith_sat_id: CP.t -> bool * ((CP.t * CP.t) list)

val arith_sat_abduce: CP.t -> bool * ((CP.t * CP.t) list)
