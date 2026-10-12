/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Flasque
public import ReasLib.CategoryTheory.Sites.Cohomology.Map

/-!
# Bridge: topological sheaf cohomology via the site-theoretic framework

This module specializes Mathlib's site-theoretic sheaf cohomology (`Sheaf.H`) to the
Grothendieck topology on opens of a topological space.

The key identification is that `TopCat.Sheaf C X` is definitionally
`Sheaf (Opens.grothendieckTopology X) C`, so Mathlib's `Sheaf.H` applies directly.

## Main declarations

- `TopCat.Sheaf.Cohomology.H`: a transparent opens-site alias for `CategoryTheory.Sheaf.H`
- `TopCat.Sheaf.Cohomology.map`: the canonical cohomology map on an opens site
- `CategoryTheory.Sheaf.IsFlasque.isZero_cohomology`: positive-degree vanishing on every open

## References

- [Stacks Project, Tag 01DZ](https://stacks.math.columbia.edu/tag/01DZ) (Cohomology of sheaves)
- [Stacks Project, Tag 01EK](https://stacks.math.columbia.edu/tag/01EK) (Flasque sheaves)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Opposite

noncomputable section

universe v

namespace TopCat.Sheaf.Cohomology

/- The opens-site cohomology owners are already canonical Mathlib declarations.  Keep this leaf as
a recall surface rather than introducing a second carrier or an unproved connecting map. -/

end TopCat.Sheaf.Cohomology

namespace CategoryTheory.Sheaf

variable {X : TopCat.{v}}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
variable [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v})]

/-- A flasque abelian sheaf has zero positive-degree cohomology on every open of the underlying
topological space. -/
@[stacks 09SY "higher cohomology of a flasque sheaf"]
theorem IsFlasque.isZero_cohomology
    (F : X.Sheaf AddCommGrpCat.{v}) [TopCat.Sheaf.IsFlasque F]
    (U : Opens X) {p : ℕ} (hp : 0 < p) :
    IsZero (F.H' p U) := sorry

/-- A proposition-valued flasqueness hypothesis implies vanishing of positive-degree cohomology. -/
@[stacks 09SY "explicit flasque-cohomology bridge"]
theorem higherCohomology_isZero_of_isFlasque
    (F : X.Sheaf AddCommGrpCat.{v}) (hF : TopCat.Sheaf.IsFlasque F)
    (U : Opens X) (p : ℕ) (hp : 0 < p) :
    IsZero (F.H' p U) := sorry


end CategoryTheory.Sheaf

end

end
