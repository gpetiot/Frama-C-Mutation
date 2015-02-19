
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

(* StaDy *)

module Int_for_collection = struct
  include Datatype.Int
  let of_string = int_of_string
  let to_string = string_of_int
  let of_singleton_string = Self.no_element_of_string
end

module Int_list(X: Parameter_sig.Input_with_arg) =
  Self.Make_list
    (Int_for_collection)
    (struct include X let default = [] end)

module Contract_weakness_detection =
  Int_list
    (struct
      let option_name = "-mut-cwd"
      let help = "identifiers of statement to check for contract weakness"
      let arg_name = "i,..."
    end)

(* Debug Keys *)

let dkey_progress = Self.register_category "progress"
let dkey_report = Self.register_category "report"
let dkey_mutant = Self.register_category "mutant"
