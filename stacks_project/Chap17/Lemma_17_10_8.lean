/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Local
import StacksCheckRecall

/-!
# Quasi-coherent modules are locally associated

The reusable pointwise and locally compact forms of the result live in
`RingedSpace.Module.Associated`. This chapter file records the source correspondence.
-/

@[expose] public section

open TopologicalSpace
open scoped AlgebraicGeometry Topology

namespace AlgebraicGeometry

open RingedSpace.Module

/- Lemma 17.10.8 (01BK): a quasi-coherent `O_X`-module is associated on some open neighborhood
of any point having a basis of compact neighborhoods. -/
@[stacks 01BK] #check @Associated.IsAssociatedAt.ofIsQuasicoherent

#check @Associated.IsAssociatedOn
#check @Associated.IsAssociatedOn.mono
#check @Associated.IsAssociatedAt
#check @Associated.IsLocallyAssociated.ofIsQuasicoherent

end AlgebraicGeometry
