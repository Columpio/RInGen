[<AutoOpen>]
module RInGen.Options

let mutable SECONDS_TIMEOUT = 5 * 60
let MSECONDS_TIMEOUT () = SECONDS_TIMEOUT * 1000
let MEMORY_LIMIT_MB = 8L * (1L <<< 10)

type MODES = VERBOSE_MODE | QUIET_MODE | EXTRA_VERBOSE_MODE
let mutable VERBOSITY_MODE = VERBOSE_MODE
let IN_QUIET_MODE () = VERBOSITY_MODE = QUIET_MODE
let IN_VERBOSE_MODE () = VERBOSITY_MODE = VERBOSE_MODE || VERBOSITY_MODE = EXTRA_VERBOSE_MODE
let IN_EXTRA_VERBOSE_MODE () = VERBOSITY_MODE = EXTRA_VERBOSE_MODE

let print_verbose (format : string) : unit =
    if IN_VERBOSE_MODE () then printfn $"%s{format}" else ()

let print_extra_verbose (format : string) : unit =
    if IN_EXTRA_VERBOSE_MODE () then printfn $"%s{format}" else ()

let print_err_verbose (format : string) : unit =
    print_verbose $"Error: %s{format}"

let print_warn_verbose (format : string) : unit =
    print_verbose $"Warning: %s{format}"

let failwith_verbose (format : string) : 'T =
    if IN_VERBOSE_MODE () then failwith format else Unchecked.defaultof<'T>

type transformOptions = {tip: bool; sync_terms: bool; no_isolation: bool}
type solvingOptions = {keep_exists: bool; table: bool}
