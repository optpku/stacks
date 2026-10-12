/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import stacks_project.Chap63.Lemma_63_3_17_Comparison

/-!
# Stalk formula and exactness for étale lower shriek

Lemma 63.3.17: if `f : X ⟶ Y` is separated and locally quasi-finite, then
functorially in abelian étale sheaves `F` the stalk `(f_! F)_ȳ` is the
coproduct of the stalks `F_x̄` over same-field geometric points of `X` with
`f(x̄) = ȳ`, and the functor `f_!` is exact.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyQuasiFinite f]
  [LocallyOfFiniteType f]

section StalkIso

variable (ybar : GeometricPoint Y)

/-- Lemma 63.3.17 (1): Let `f : X ⟶ Y` be a morphism of schemes which is
separated and locally quasi-finite. Then for `F` in `Ab(X_étale)` and a
geometric point `ȳ : Spec k ⟶ Y` we have `(f_! F)_ȳ = ⊕_{f(x̄)=ȳ} F_x̄`
functorially in `F`. -/
@[stacks 0F57]
def etaleLowerShriekStalkIso :
    etaleLowerShriek f ⋙ (toSmallEtalePoint ybar).sheafFiber ≅
      abelianStalkCoproduct f ybar where
  hom := etaleLowerShriekStalkComparison f ybar
  inv := etaleLowerShriekStalkComparisonInv f ybar
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The identification of Lemma 63.3.17 (1) at an abelian étale sheaf `F`. -/
def etaleLowerShriekStalkIso_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (toSmallEtalePoint ybar).sheafFiber.obj ((etaleLowerShriek f).obj F) ≅
      (abelianStalkCoproduct f ybar).obj F :=
  (etaleLowerShriekStalkIso f ybar).app F

/-- The forward map of `etaleLowerShriekStalkIso` is the compact-support germ
comparison. -/
theorem etaleLowerShriekStalkIso_hom :
    (etaleLowerShriekStalkIso f ybar).hom =
      etaleLowerShriekStalkComparison f ybar :=
  rfl

/-- The inverse map of `etaleLowerShriekStalkIso` is the coproduct of the stalk
legs `etaleLowerShriekStalkι`. -/
theorem etaleLowerShriekStalkIso_inv :
    (etaleLowerShriekStalkIso f ybar).inv =
      etaleLowerShriekStalkComparisonInv f ybar :=
  rfl

end StalkIso

/-- Étale lower shriek along a separated locally quasi-finite morphism preserves
finite limits. -/
instance etaleLowerShriek_preservesFiniteLimits :
    PreservesFiniteLimits (etaleLowerShriek f) :=
  sorry

/-- Étale lower shriek along a separated locally quasi-finite morphism preserves
finite colimits. -/
instance etaleLowerShriek_preservesFiniteColimits :
    PreservesFiniteColimits (etaleLowerShriek f) :=
  sorry

/-- Lemma 63.3.17 (2): Let `f : X ⟶ Y` be a morphism of schemes which is
separated and locally quasi-finite. Then the functor `f_!` is exact. -/
@[stacks 0F57]
theorem etaleLowerShriek_exact :
    exactFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (etaleLowerShriek f) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
