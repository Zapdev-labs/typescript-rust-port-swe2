// Ported from tsc/internal/packagejson/validated.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use crate::expected::{Expected, ExpectedJSONType};

/// `type TypeValidatedField interface`
///
/// PORT: Go's structural interface becomes an explicit trait; `Expected[T]`
/// implements it when `T` declares its expected JSON type.
pub trait TypeValidatedField {
    /// `IsPresent() bool`
    fn is_present(&self) -> bool;
    /// `IsValid() bool`
    fn is_valid(&self) -> bool;
    /// `ExpectedJSONType() string`
    fn expected_json_type(&self) -> &'static str;
    /// `ActualJSONType() string`
    fn actual_json_type(&self) -> &'static str;
}

// `Expected[T]` satisfies `TypeValidatedField` structurally in Go.
impl<T: ExpectedJSONType> TypeValidatedField for Expected<T> {
    fn is_present(&self) -> bool {
        self.is_present()
    }

    fn is_valid(&self) -> bool {
        self.is_valid()
    }

    fn expected_json_type(&self) -> &'static str {
        T::expected_json_type()
    }

    fn actual_json_type(&self) -> &'static str {
        self.actual_json_type()
    }
}
