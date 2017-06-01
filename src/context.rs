use std::collections::BTreeMap;

/// A context hold values for variables, that can be used to evaluate
/// expressions.
///
/// # Examples
///
/// ```
/// # use caldyn::Context;
/// let mut context = Context::new();
/// context.set("a", 3.0);
/// context.set("b", -2.5);
///
/// assert_eq!(context.get("a"), Some(3.0));
/// assert_eq!(context.get("d"), None);
/// ```
pub struct Context {
    values: BTreeMap<String, f64>,
}

impl Context {
    /// Create a new empty context
    pub fn new() -> Context {
        Context {
            values: BTreeMap::new()
        }
    }

    /// Set a variable with the given `name` and `value`. If the variable
    /// already exists, the value is updated.
    ///
    /// # Examples
    ///
    /// ```
    /// # use caldyn::Context;
    /// let mut context = Context::new();
    /// context.set("a", 3.0);
    /// assert_eq!(context.get("a"), Some(3.0));
    /// assert_eq!(context.get("d"), None);
    ///
    /// context.set("d", 5.0);
    /// context.set("a", 8.0);
    /// assert_eq!(context.get("a"), Some(8.0));
    /// assert_eq!(context.get("d"), Some(5.0));
    /// ```
    pub fn set<S: Into<String>>(&mut self, name: S, value: f64) {
        self.values.insert(name.into(), value);
    }

    /// Get the value of the variable with `name`, or `None` if the variable
    /// is not defined.
    ///
    /// # Examples
    ///
    /// ```
    /// # use caldyn::Context;
    /// let mut context = Context::new();
    /// context.set("a", 3.0);
    /// assert_eq!(context.get("a"), Some(3.0));
    /// assert_eq!(context.get("d"), None);
    /// ```
    pub fn get(&self, name: &str) -> Option<f64> {
        self.values.get(name).cloned()
    }
}
