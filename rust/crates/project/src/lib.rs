// Ported from tsc/internal/project @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The project/session layer above `tsc-ls`: Project, Snapshot,
// ProjectCollection, Session, overlay/snapshot VFS, checker pools, and the
// `ata` (automatic type acquisition) + `background` subpackages.

pub mod ata;
pub mod background;

pub mod api;
pub mod autoimport;
pub mod checkerpool;
pub mod client;
pub mod compilerhost;
pub mod configfileregistry;
pub mod configfileregistrybuilder;
pub mod extendedconfigcache;
pub mod filechange;
pub mod overlayfs;
pub mod ownercache;
pub mod parsecache;
pub mod programcounter;
pub mod project;
pub mod project_stringer_generated;
pub mod projectcollection;
pub mod projectcollectionbuilder;
pub mod refcountcache;
pub mod session;
pub mod snapshot;
pub mod snapshotfs;
pub mod snapshothost;
pub mod watch;
