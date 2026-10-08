// Ported from tsc/internal/core/typeacquisition.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use crate::options_generated::TypeAcquisition;

impl TypeAcquisition {
    // PORT: Go's nilable `*TypeAcquisition` receiver/argument becomes
    // `Option<&TypeAcquisition>` parameters.
    pub fn equals(ta: Option<&TypeAcquisition>, other: Option<&TypeAcquisition>) -> bool {
        match (ta, other) {
            (Some(a), Some(b)) if std::ptr::eq(a, b) => return true,
            (None, None) => return true,
            (None, _) | (_, None) => return false,
            _ => {}
        }
        let (Some(ta), Some(other)) = (ta, other) else {
            unreachable!()
        };

        // PORT: `slices.Equal(nil, empty)` is true in Go, so nilable
        // Option<Vec<_>> fields compare via as_deref().unwrap_or(&[]).
        ta.enable == other.enable
            && ta.include.as_deref().unwrap_or(&[]) == other.include.as_deref().unwrap_or(&[])
            && ta.exclude.as_deref().unwrap_or(&[]) == other.exclude.as_deref().unwrap_or(&[])
            && ta.disable_filename_based_type_acquisition
                == other.disable_filename_based_type_acquisition
    }
}
