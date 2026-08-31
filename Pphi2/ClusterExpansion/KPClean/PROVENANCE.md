# Clean-room provenance

The finite polymer definitions in `Core.lean` are newly authored for this
repository.  They use the finite-volume formulation of the Kotecký--Preiss
criterion from R. Kotecký and D. Preiss, “Cluster expansion for abstract
polymer models,” *Communications in Mathematical Physics* **103** (1986),
491–498.  The implementation method is a direct formalization of the
published definitions: a finite polymer volume, a symmetric reflexive
incompatibility relation, compatible collections, activity products, the
finite partition sum, and the absolute-activity KP row condition.

The later rooted cluster estimate is intentionally outside this packet.  The
rooted and pinned collection sums expose its finite input boundary, while the
signed-activity `ENNReal` majorant records the separate domination interface
needed by the continuous-spin activity proof.

No file from the recovered mirror-derived `ClusterExpansion/KP/` tree was read,
copied, imported, or used as an implementation source for this directory.
The clean branch inherits repository history that predates this packet.  That
historical ancestry is not an authorship claim for the new definitions and is
kept separate from the active source path, which contains only `KPClean`.
