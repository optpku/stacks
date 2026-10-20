module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Underlying
public import ReasLib.CategoryTheory.Sites.Cohomology.LocallyZero
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local vanishing of positive module cohomology classes

This leaf is the ringed-space specialization of the site-level cover-vanishing theorem.  It keeps
the underlying additive cohomology presentation used by the textbook while exposing it from the
`ModuleCohomology` namespace, so later arguments do not import a Chapter 20 file.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleCohomology

variable {X : RingedSpace.{u}}
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/-- Lemma 20.7.2 (01E3): every positive-degree cohomology class of a module sheaf becomes zero
after restriction to every arrow of a suitable cover of the chosen open. -/
@[stacks 01E3 "positive cohomology classes vanish on a cover"]
theorem existsCoverRestrictEqZero
    (F : X.Modules) {U : Opens X.carrier} {n : ℕ} (hn : 0 < n)
    (xi : ((moduleUnderlyingSheaf X).obj F).H' n U) :
    ∃ T : (Opens.grothendieckTopology X.carrier).Cover U, ∀ I : T.Arrow,
      ((((moduleUnderlyingSheaf X).obj F).cohomologyPresheaf n).map I.f.op) xi = 0 := sorry

end AlgebraicGeometry.RingedSpace.ModuleCohomology

end
