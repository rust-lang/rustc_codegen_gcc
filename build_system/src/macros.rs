macro_rules! arg_error {
    ($($err:tt)*) => {{
        eprintln!($($err)*);
        eprintln!();
        usage();
        std::process::exit(1);
    }};
}

macro_rules! commands_decl {
    (__inner, $command_name:literal) => {
        println!(concat!("`", $command_name, "` command help:"));
    };
    (__inner, ) => {
        println!("rustc_codegen_gcc build system

Usage: build_system [command] [options]

Options:
    --help     : Displays this help message.

Commands:");
    };
    (
        $name:ident $(=> $command_name:literal)?,
        $($variant:ident: $doc_name:literal => $doc:literal ,)+
    ) => {
        enum $name {
            $($variant),+
        }

        impl<'a> From<Option<&'a str>> for $name {
            fn from(arg: Option<&'a str>) -> Self {
                match arg {
                    $(Some($doc_name) => Self::$variant,)+
                    Some("--help") => {
                        usage();
                        std::process::exit(0);
                    }
                    Some(flag) if flag.starts_with('-') => arg_error!("Expected command found flag {}", flag),
                    Some(command) => arg_error!("Unknown command {}", command),
                    None => {
                        usage();
                        std::process::exit(0);
                    }
                }
            }
        }

        fn usage() {
            commands_decl!(__inner, $($command_name)?);
            crate::utils::show_help_with_indent(vec![$(($doc_name.to_string(), $doc),)+], false);
        }
    }
}
