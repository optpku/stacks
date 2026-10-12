/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Category.ProfiniteGrp.Recognition
import StacksCheckRecall

@[expose] public section

/- Definition 5.30.5: `ProfiniteGrp` is the canonical bundled owner for profinite topological
groups. The two shared bridge theorems recover the corresponding unbundled formulations. -/
@[stacks 0BR2 "profinite topological groups"]
#check ProfiniteGrp

/- An unbundled topological group is homeomorphic to a profinite space exactly when it is
continuously group-isomorphic to a bundled profinite group. -/
@[stacks 0BR2 "profinite topological group recognition by a bundled model"]
#check ProfiniteGrp.exists_homeomorph_iff_exists_continuousMulEquiv

/- The bundled profinite-group model is equivalent to compactness and total disconnectedness. -/
@[stacks 0BR2 "compact totally disconnected recognition of profinite groups"]
#check ProfiniteGrp.exists_continuousMulEquiv_iff_compact_totallyDisconnected
