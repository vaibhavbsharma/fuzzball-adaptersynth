val syscalls_x64: ( int * string ) array 

class noop_linux_special_handler : Fragment_machine.fragment_machine ->
object
  method handle_special : string -> Vine.stmt list option
  method make_snap : unit
  method reset : unit
  method make_f1_snap : unit
  method reset_f1_snap : unit
  method make_f2_snap : unit
  method reset_f2_snap : unit
end
