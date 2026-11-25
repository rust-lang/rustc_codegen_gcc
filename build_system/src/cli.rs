use std::collections::BTreeMap;

type FlagFn<O> = Box<dyn Fn(&mut O) -> Result<(), String>>;
type ArgFn<O> = Box<dyn Fn(&mut O, String) -> Result<(), String>>;
type MultiArgFnRes<O> = Box<dyn Fn(&mut O, &mut dyn Iterator<Item = String>) -> Result<(), String>>;
type MultiArgFn<O> = Box<dyn Fn(&mut O, &mut dyn Iterator<Item = String>)>;

/// This struct is used to declare and parse CLI arguments.
pub struct ArgsHandler<O> {
    handlers: BTreeMap<String, ArgHandler<O>>,
    command_name: &'static str,
    fallback: Option<MultiArgFn<O>>,
}

struct ArgHandler<O> {
    handler: ArgKind<O>,
    help: String,
}

enum ArgKind<O> {
    /// No argument.
    Flag(FlagFn<O>),
    /// One argument.
    Arg { callback: ArgFn<O>, allow_empty: bool },
    /// Undefined number of arguments.
    Multi(MultiArgFnRes<O>),
}

impl<O: 'static> ArgKind<O> {
    /// Wraps the callback so it runs on a `Parent` and writes to the field `get_field` returns.
    fn convert_to_parent<Parent: 'static>(
        self,
        get_field: fn(&mut Parent) -> &mut O,
    ) -> ArgKind<Parent> {
        match self {
            ArgKind::Flag(callback) => {
                ArgKind::Flag(Box::new(move |parent: &mut Parent| callback(get_field(parent))))
            }
            ArgKind::Arg { callback, allow_empty } => ArgKind::Arg {
                callback: Box::new(move |parent: &mut Parent, arg| {
                    callback(get_field(parent), arg)
                }),
                allow_empty,
            },
            ArgKind::Multi(callback) => {
                ArgKind::Multi(Box::new(move |parent: &mut Parent, args| {
                    callback(get_field(parent), args)
                }))
            }
        }
    }

    fn extra_help_word(&self) -> Option<&'static str> {
        match self {
            ArgKind::Flag(_) => None,
            ArgKind::Arg { .. } => Some("[arg]"),
            ArgKind::Multi(_) => Some("[args...]"),
        }
    }
}

impl<O: Default + 'static> ArgsHandler<O> {
    pub fn new(command_name: &'static str) -> Self {
        Self { handlers: BTreeMap::new(), command_name, fallback: None }
    }

    /// Used to handle a flag (ie an argument without an associated value). `callback` is called
    /// when processed so you can run an associated action for this flag (like setting a type's
    /// field).
    pub fn with_flag<F: Fn(&mut O) + 'static>(
        mut self,
        name: &str,
        help: &str,
        callback: F,
    ) -> Self {
        if self
            .handlers
            .insert(
                name.to_string(),
                ArgHandler {
                    handler: ArgKind::Flag(Box::new(move |o| {
                        callback(o);
                        Ok(())
                    })),
                    help: help.to_string(),
                },
            )
            .is_some()
        {
            panic!("`{name}` is already defined in `{}`", self.command_name);
        }
        self
    }

    /// Used to handle an argument (ie an CLI arg with an associated value like `--value something`).
    /// `callback` is called when processed so you can run an associated action for this argument
    /// (like setting a type's field). It checks that the associated value is not empty.
    /// If empty, `callback` will not be called and it will emit an error.
    pub fn with_arg<F: Fn(&mut O, String) + 'static>(
        mut self,
        name: &str,
        help: &str,
        callback: F,
    ) -> Self {
        if self
            .handlers
            .insert(
                name.to_string(),
                ArgHandler {
                    handler: ArgKind::Arg {
                        callback: Box::new(move |o, s| {
                            callback(o, s);
                            Ok(())
                        }),
                        allow_empty: false,
                    },
                    help: help.to_string(),
                },
            )
            .is_some()
        {
            panic!("`{name}` is already defined in `{}`", self.command_name);
        }
        self
    }

    /// Equivalent of [`Self::with_non_empty_arg`] but the callback returns a `Result` this time.
    pub fn with_arg_res<F: Fn(&mut O, String) -> Result<(), String> + 'static>(
        mut self,
        name: &str,
        help: &str,
        callback: F,
    ) -> Self {
        if self
            .handlers
            .insert(
                name.to_string(),
                ArgHandler {
                    handler: ArgKind::Arg { callback: Box::new(callback), allow_empty: false },
                    help: help.to_string(),
                },
            )
            .is_some()
        {
            panic!("`{name}` is already defined in `{}`", self.command_name);
        }
        self
    }

    pub fn with_multi<F: Fn(&mut O, &mut dyn Iterator<Item = String>) + 'static>(
        mut self,
        name: &str,
        help: &str,
        callback: F,
    ) -> Self {
        self.handlers.insert(
            name.to_string(),
            ArgHandler {
                handler: ArgKind::Multi(Box::new(move |o, s| {
                    callback(o, s);
                    Ok(())
                })),
                help: help.to_string(),
            },
        );
        self
    }

    pub fn with_fallback<F: Fn(&mut O, &mut dyn Iterator<Item = String>) + 'static>(
        mut self,
        callback: F,
    ) -> Self {
        if self.fallback.is_some() {
            panic!("`with_fallback` was called more than once on command `{}`", self.command_name);
        }
        self.fallback = Some(Box::new(callback));
        self
    }

    /// Adds `sub`'s options as if they were declared here; their values go to the field
    /// `get_field` returns.
    pub fn with_sub_handler<S: Default + 'static>(
        mut self,
        sub: ArgsHandler<S>,
        get_field: fn(&mut O) -> &mut S,
    ) -> Self {
        for (name, ArgHandler { handler, help }) in sub.handlers {
            let handler = ArgHandler { handler: handler.convert_to_parent(get_field), help };
            if self.handlers.insert(name.clone(), handler).is_some() {
                panic!(
                    "`{name}` is defined both in `{}` and `{}`",
                    self.command_name, sub.command_name
                );
            }
        }
        self
    }

    pub fn parse_args<I: Iterator<Item = String>>(&self, mut args: I) -> Result<Option<O>, String> {
        let mut parsed = O::default();
        while let Some(arg) = args.next() {
            if arg == "--help" {
                self.show_usage();
                return Ok(None);
            } else if !self.parse_arg(&arg, &mut args, &mut parsed)? {
                return Err(format!(
                    "Unknown argument `{arg}`. Use `--help` to see the list of available options."
                ));
            }
        }
        Ok(Some(parsed))
    }

    /// Returns `Ok(false)` if the argument doesn't exist, `Ok(true)` if it exists and was parsed.
    pub fn parse_arg<I: Iterator<Item = String>>(
        &self,
        arg: &str,
        args: &mut I,
        parsed: &mut O,
    ) -> Result<bool, String> {
        if let Some(arg_handler) = self.handlers.get(arg) {
            match arg_handler.handler {
                ArgKind::Flag(ref callback) => callback(parsed)?,
                ArgKind::Arg { ref callback, allow_empty } => match args.next() {
                    Some(next_arg) if allow_empty || !next_arg.is_empty() => {
                        callback(parsed, next_arg)?
                    }
                    _ => return Err(format!("Expected a value after `{arg}`, found nothing")),
                },
                ArgKind::Multi(ref callback) => callback(parsed, args)?,
            }
            Ok(true)
        } else if let Some(ref fallback) = self.fallback {
            fallback(parsed, args);
            Ok(true)
        } else {
            Ok(false)
        }
    }

    fn show_usage(&self) {
        println!(
            "rustc_codegen_gcc build system

Usage: build_system{}

Options:",
            if self.command_name.is_empty() { "" } else { " " }
        );

        // `+ 1` because we add the `--help` in `show_help_with_indent`.
        let mut commands = Vec::with_capacity(self.handlers.len() + 1);
        for (arg_name, handler) in &self.handlers {
            let name = if let Some(extra) = handler.handler.extra_help_word() {
                format!("{arg_name} {extra}")
            } else {
                arg_name.clone()
            };
            commands.push((name, handler.help.as_str()));
        }
        crate::utils::show_help_with_indent(commands, true);
    }
}

type UniqueFlagFn<O> = Box<dyn Fn() -> O>;

/// This struct is used to declare and parse one CLI command.
pub struct CommandsHandler<O> {
    handlers: BTreeMap<&'static str, CommandHandler<O>>,
    command_name: &'static str,
}

struct CommandHandler<O> {
    handler: UniqueFlagFn<O>,
    help: &'static str,
}

impl<O: 'static> CommandsHandler<O> {
    pub fn new(command_name: &'static str) -> Self {
        Self { handlers: BTreeMap::new(), command_name }
    }

    pub fn with_flag<F: Fn() -> O + 'static>(
        mut self,
        name: &'static str,
        help: &'static str,
        callback: F,
    ) -> Self {
        if self
            .handlers
            .insert(name, CommandHandler { handler: Box::new(callback), help })
            .is_some()
        {
            panic!("`{name}` is already defined in `{}`", self.command_name);
        }
        self
    }

    pub fn parse_args<I: Iterator<Item = String>>(&self, mut args: I) -> Option<O> {
        if let Some(arg) = args.next() {
            if arg == "--help" {
                self.show_usage();
                None
            } else if let Some(arg_handler) = self.handlers.get(arg.as_str()) {
                Some((arg_handler.handler)())
            } else {
                eprintln!("Unknown command `{arg}`");
                eprintln!();
                self.show_usage();
                std::process::exit(1);
            }
        } else {
            self.show_usage();
            None
        }
    }

    fn show_usage(&self) {
        println!(
            "rustc_codegen_gcc build system

Usage: build_system {}

Options:
    --help     : Displays this help message.

Commands:",
            self.command_name,
        );
        // `+ 1` because we add the `--help` in `show_help_with_indent`.
        let mut commands = Vec::with_capacity(self.handlers.len() + 1);
        for (arg_name, handler) in &self.handlers {
            commands.push((arg_name.to_string(), handler.help));
        }
        crate::utils::show_help_with_indent(commands, false);
    }
}
