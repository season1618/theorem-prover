let var_count = ref(0)

let fresh_var () =
  var_count := !var_count + 1;
  "_" ^ string_of_int !var_count
