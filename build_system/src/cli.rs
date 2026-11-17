use std::collections::BTreeMap;

pub struct ArgsHandler<O: Default> {
    handlers: BTreeMap<String, ArgHandler<O>>,
    command_name: &'static str,
}

pub struct ArgHandler<O> {
    handler: ArgKind<O>,
    help: String,
}

pub type FlagFn<O> = Box<dyn Fn(&mut O) -> Result<(), String>>;
pub type ArgFn<O> = Box<dyn Fn(&mut O, String) -> Result<(), String>>;

pub enum ArgKind<O> {
    /// No argument.
    Flag(FlagFn<O>),
    /// One argument.
    Arg { callback: ArgFn<O>, allow_empty: bool },
    // /// Undefined number of arguments.
    // Multi(fn(&mut O, &mut dyn Iterator<Item = String>) -> Result<(), String>),
}

impl<O: 'static> ArgKind<O> {
    /// Used in `ArgsHandler::with_sub_handler`: it allows to convert the current handlers to the
    /// parent's closures so they can all be handled at once.
    fn convert_to_parent<S: 'static>(self, lifter_callback: fn(&mut S) -> &mut O) -> ArgKind<S> {
        match self {
            ArgKind::Flag(callback) => {
                ArgKind::Flag(Box::new(move |parent: &mut S| callback(lifter_callback(parent))))
            }
            ArgKind::Arg { callback, allow_empty } => ArgKind::Arg {
                callback: Box::new(move |parent: &mut S, arg| {
                    callback(lifter_callback(parent), arg)
                }),
                allow_empty,
            },
            // ArgKind::Multi(callback) => ArgKind::Multi(Box::new(move |o: &mut S, args| callback(lifter_callback(o), args))),
        }
    }

    fn extra_help_word(&self) -> Option<&'static str> {
        match self {
            ArgKind::Flag(_) => None,
            ArgKind::Arg { .. } => Some("[arg]"),
        }
    }
}

impl<O: Default + 'static> ArgsHandler<O> {
    pub fn new(command_name: &'static str) -> Self {
        Self { handlers: BTreeMap::new(), command_name }
    }

    pub fn with_flag<F: Fn(&mut O) -> Result<(), String> + 'static>(
        mut self,
        name: &str,
        help: &str,
        callback: F,
    ) -> Self {
        if self
            .handlers
            .insert(
                name.to_string(),
                ArgHandler { handler: ArgKind::Flag(Box::new(callback)), help: help.to_string() },
            )
            .is_some()
        {
            panic!("`{name}` is already defined in `{}`", self.command_name);
        }
        self
    }

    pub fn with_arg<F: Fn(&mut O, String) -> Result<(), String> + 'static>(
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
                    handler: ArgKind::Arg { callback: Box::new(callback), allow_empty: true },
                    help: help.to_string(),
                },
            )
            .is_some()
        {
            panic!("`{name}` is already defined in `{}`", self.command_name);
        }
        self
    }

    pub fn with_non_empty_arg<F: Fn(&mut O, String) -> Result<(), String> + 'static>(
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

    // pub fn with_multi(
    //     mut self,
    //     name: &str,
    //     help: &str,
    //     callback: fn(&mut O, &mut dyn Iterator<Item = String>) -> Result<(), String>,
    // ) -> Self {
    //     self.handlers.insert(
    //         name.to_string(),
    //         ArgHandler { handler: ArgKind::Multi(callback), help: help.to_string() },
    //     );
    //     self
    // }

    /// Add a sub args handlers into the current one. A good example of usage is the `ConfigInfo`
    /// struct used in multiple places with its own `ArgsHandler`. You don't want to duplicate its
    /// fields nor its arguments parsing, so instead we call the `ArgKind::convert_to_parent`
    /// method on each handler so they can be integrated directly into `self`.
    pub fn with_sub_handler<S: Default + 'static>(
        mut self,
        sub: ArgsHandler<S>,
        lifter_callback: fn(&mut O) -> &mut S,
    ) -> Self {
        for (name, ArgHandler { handler, help }) in sub.handlers {
            let handler = ArgHandler { handler: handler.convert_to_parent(lifter_callback), help };
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
            }
            if !self.parse_arg(&arg, &mut args, &mut parsed)? {
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
                ArgKind::Arg { ref callback, allow_empty } => {
                    let Some(next_arg) = args.next() else {
                        return Err(format!("Expected a value after `{arg}`, found nothing"));
                    };
                    if !allow_empty && next_arg.is_empty() {
                        return Err(format!("Expected a value after `{arg}`, found nothing"));
                    }
                    callback(parsed, next_arg)?
                } // ArgKind::Multi(callback) => callback(parsed, args)?,
            }
            Ok(true)
        } else {
            Ok(false)
        }
    }

    fn show_usage(&self) {
        println!("`{}` command help:\n", self.command_name);

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
