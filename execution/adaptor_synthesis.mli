
val arithmetic_int_adaptor : 
  Fragment_machine.fragment_machine -> int64 -> int64 -> unit
val arithmetic_int_extra_conditions :
  Fragment_machine.fragment_machine -> int64 -> int -> unit
val arithmetic_float_adaptor : 
  Fragment_machine.fragment_machine -> int64 -> int64 -> unit
val arithmetic_float_extra_conditions :
  Fragment_machine.fragment_machine -> int64 -> int -> unit
val simple_adaptor : 
  Fragment_machine.fragment_machine -> int64 -> int64 -> unit
val typeconv_adaptor : 
  Fragment_machine.fragment_machine -> int64 -> int64 -> unit
val float_typeconv_adaptor : 
  Fragment_machine.fragment_machine -> int64 -> int64 -> unit
val ret_typeconv_adaptor :
  Fragment_machine.fragment_machine -> int64 -> unit
val ret_simplelen_adaptor :
  Fragment_machine.fragment_machine -> int64 -> unit
val create_field_ranges_l : 
  Fragment_machine.fragment_machine -> unit 
val arithmetic_int_init_sym_vars : Fragment_machine.fragment_machine -> int -> unit 
val i_array_field_ranges_l' : (int * int * int * int * int * Vine.exp) list ref
val ranges_by_field_num : int64 list ref array ref
val struct_adaptor: 
  Fragment_machine.fragment_machine -> unit
val adaptor_score : int ref
