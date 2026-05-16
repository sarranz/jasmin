val tt_prim :
  (string -> exn) ->
  (string * 'a Sopn.prim_constructor) list ->
  string ->
  Sopn.prim_x86_suffix option ->
  'a
