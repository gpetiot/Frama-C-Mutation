
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

module Mut_Spec = Self.True (struct
  let option_name = "-mut-spec"
  let help = "perform mutations on the ACSL specification"
end)

module Only = Self.Int (struct
  let option_name = "-mut-only"
  let help = "only perform a given mutation (designated by its number)"
  let arg_name = "N"
  let default = -1
end)

module Summary_File = Self.String (struct
  let option_name = "-mut-summary-file"
  let help = "write the summary of generated mutations in a file"
  let arg_name = "F"
  let default = "summary.csv"
end)

(* Debug Keys *)

let dkey_progress = Self.register_category "progress"
let dkey_mutant = Self.register_category "mutant"
