
val arithmetic_int_adapter : 
  Fragment_machine.fragment_machine -> int64 -> int64 -> unit
val arithmetic_int_extra_conditions :
  Fragment_machine.fragment_machine -> int64 -> int -> unit
val arithmetic_float_adapter : 
  Fragment_machine.fragment_machine -> int64 -> int64 -> unit
val arithmetic_float_extra_conditions :
  Fragment_machine.fragment_machine -> int64 -> int -> unit
val simple_adapter : 
  Fragment_machine.fragment_machine -> int64 -> int64 -> unit
val typeconv_adapter : 
  Fragment_machine.fragment_machine -> int64 -> int64 -> unit
val float_typeconv_adapter : 
  Fragment_machine.fragment_machine -> int64 -> int64 -> unit
val ret_typeconv_adapter :
  Fragment_machine.fragment_machine -> int64 -> unit
val ret_simplelen_adapter :
  Fragment_machine.fragment_machine -> int64 -> unit
val create_field_ranges_l : 
  Fragment_machine.fragment_machine -> unit 
val arithmetic_int_init_sym_vars : Fragment_machine.fragment_machine -> int -> unit 
val i_array_field_ranges_l' : (int * int * int * int * int * Vine.exp) list ref
val ranges_by_field_num : int64 list ref array ref
val struct_adapter: 
  Fragment_machine.fragment_machine -> unit
val adapter_score : int ref
