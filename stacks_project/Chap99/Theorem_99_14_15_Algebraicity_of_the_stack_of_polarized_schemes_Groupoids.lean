/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import stacks_project.Chap99.Lemma_99_14_8_Groupoids
public import stacks_project.Chap99.Remark_99_14_5

/-!
# The category `B`-Polarized as a groupoid fibration

The pair category `B`-Polarized of Remark 99.14.5 is packaged as a category
fibred in groupoids over `Over specZ`, at Hom-universe `u`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- The forgetful functor of `B`-Polarized, sending a polarized object equipped
with a morphism from its base scheme into `B` to that base scheme as an object
of `Over specZ`. -/
def polarizedOver.p (B : AlgebraicSpace specZ) :
    polarizedOver B ⥤ Over specZ :=
  (polarizedOver.square B).fst ⋙ Polarized.p ⋙ toOverSpecZ

/-- The projection `polarizedOver.p B` is the first projection of the
2-fibre-product square of Remark 99.14.5, followed by `Polarized.p ⋙ toOverSpecZ`. -/
theorem polarizedOver.p_eq (B : AlgebraicSpace specZ) :
    polarizedOver.p B =
      (polarizedOver.square B).fst ⋙ Polarized.p ⋙ toOverSpecZ :=
  sorry

/-- The forgetful functor of `B`-Polarized is fibred in groupoids over
`Over specZ`. -/
instance polarizedOver.instIsFiberedInGroupoids (B : AlgebraicSpace specZ) :
    Functor.IsFibered.InGroupoids (polarizedOver.p B) :=
  sorry

/-- The category `B`-Polarized, bundled as a category fibred in groupoids over
`Over specZ`. The Hom-universe is `u`, matching `toGroupoidsOverSpecZ`. -/
def polarizedOver.toGroupoids (B : AlgebraicSpace specZ) : GroupoidsOver specZ :=
  FiberedCategoryOver.Groupoids.ofFunctor.{u + 1, u, u + 1, u}
    (polarizedOver.p B)

/-- The projection of `polarizedOver.toGroupoids B` is the forgetful functor
`polarizedOver.p B`. -/
theorem polarizedOver.toGroupoids_p (B : AlgebraicSpace specZ) :
    (polarizedOver.toGroupoids B).p = polarizedOver.p B :=
  sorry

/-- The total category of `polarizedOver.toGroupoids B` is the pair category
`polarizedOver B` of Remark 99.14.5. -/
theorem polarizedOver.toGroupoids_total (B : AlgebraicSpace specZ) :
    (polarizedOver.toGroupoids B).total = polarizedOver B :=
  sorry

end AlgebraicGeometry.Polarized
