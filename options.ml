
module Self = Plugin.Register (struct
  let name = "Mutation"
  let shortname = "mut"
  let help = ""
end)
  
module Enabled = Self.False (struct
  let option_name = "-mut"
  let help = ""
end)

(* Customization *)

module Mut_Code = Self.True (struct
  let option_name = "-mut-code"
  let help = "perform mutations on the C code"
end)

module Only = Self.Int (struct
  let option_name = "-mut-only"
  let help = "only perform a given mutation (designated by its number)"
  let arg_name = "N"
  let default = -1
end)

module Apply_to_Mutant = Self.String (struct
  let option_name = "-mut-apply"
  let help = "plugin(s) to apply to mutants"
  let arg_name = "str"
  let default = ""
end)

(* Debug Keys *)

let dkey_progress = Self.register_category "progress"
let dkey_report = Self.register_category "report"
let dkey_mutant = Self.register_category "mutant"
