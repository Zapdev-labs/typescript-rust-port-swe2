// Ported from tsc/internal/project @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The project/session layer above `tsc-ls`: Project, Snapshot,
// ProjectCollection, Session, overlay/snapshot VFS, checker pools, and the
// `ata` (automatic type acquisition) + `background` subpackages.

pub mod ata;
pub mod background;

mod api;
mod autoimport;
mod checkerpool;
mod client;
mod compilerhost;
mod configfileregistry;
mod configfileregistrybuilder;
mod extendedconfigcache;
mod filechange;
mod overlayfs;
mod ownercache;
mod parsecache;
mod programcounter;
mod project;
mod project_stringer_generated;
mod projectcollection;
mod projectcollectionbuilder;
mod refcountcache;
mod session;
mod snapshot;
mod snapshotfs;
mod snapshothost;
mod watch;
