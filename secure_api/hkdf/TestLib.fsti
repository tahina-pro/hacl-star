module TestLib

open FStar.HyperStack.ST

val compare_and_print: string -> expected:Seq.seq UInt8.t -> actual:Seq.seq UInt8.t -> St unit
