

module Self = Plugin.Register (struct
  let name = "Mutation"
  let shortname = "mut"
  let help = ""
end)
  
module Enabled = Self.False (struct
  let option_name = "-mut"
  let help = ""
end)

(* customization *)

module Mutate_Int_Arith = Self.True (struct
  let option_name = "-mut-int-arith"
  let help = "mutate arithmetical operations over intergers"
end)
module Mutate_Ptr_Arith = Self.True (struct
  let option_name = "-mut-ptr-arith"
  let help = "mutate arithmetical operations over pointers"
end)
module Mutate_Logic_And_Or = Self.True (struct
  let option_name = "-mut-logic-and-or"
  let help = "mutate logic operations"
end)
module Mutate_Comp = Self.True (struct
  let option_name = "-mut-comp"
  let help = "mutate comparison operations"
end)
module Mutate_Lval = Self.False (struct
  let option_name = "-mut-lval"
  let help = "mutate lval into another lval in the same scope"
end)
module Mutate_Cond = Self.True (struct
  let option_name = "-mut-cond"
  let help = "negate conditions"
end)

module Only = Self.Int (struct
  let option_name = "-mut-only"
  let help = "only perform a given mutation (designated by its number)"
  let arg_name = "N"
  let default = -1
end)
