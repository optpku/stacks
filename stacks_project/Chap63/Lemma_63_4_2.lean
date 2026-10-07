module

public import stacks_project.Chap63.Lemma_63_4_2_Comparison
public import stacks_project.Chap63.Lemma_63_4_2_StalkCoproduct

/-!
# Stalk formula for the compact-support presheaf

Lemma 63.4.2: for a locally quasi-finite morphism `f : X ⟶ Y` and a geometric
point `ȳ` of `Y`, there is a canonical identification
`(f_{p!} F)_ȳ ≅ ⊕_{f(x̄)=ȳ} F_x̄`, functorial in abelian étale sheaves `F` on `X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
  [LocallyOfFiniteType f]
variable (ybar : GeometricPoint Y)

/-- Lemma 63.4.2: Let `f : X ⟶ Y` be a morphism of schemes which is locally
quasi-finite. Let `ȳ : Spec k ⟶ Y` be a geometric point. Functorially in
`F` in `Ab(X_étale)` we have `(f_{p!} F)_ȳ ≅ ⊕_{f(x̄)=ȳ} F_x̄`.
Stacks locally quasi-finite is rendered as `[LocallyQuasiFinite f]` together
with `[LocallyOfFiniteType f]`. -/
@[stacks 0F6P]
def lowerShriekPresheafStalkIso :
    lowerShriekPresheaf f ⋙ (toSmallEtalePoint ybar).presheafFiber ≅
      abelianStalkCoproduct f ybar where
  hom := lowerShriekPresheafStalkComparison f ybar
  inv := lowerShriekPresheafStalkComparisonInv f ybar
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The identification of Lemma 63.4.2 at an abelian étale sheaf `F`. -/
def lowerShriekPresheafStalkIso_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (toSmallEtalePoint ybar).presheafFiber.obj ((lowerShriekPresheaf f).obj F) ≅
      (abelianStalkCoproduct f ybar).obj F :=
  (lowerShriekPresheafStalkIso f ybar).app F

/-- The forward map of `lowerShriekPresheafStalkIso` is the germ-sum comparison. -/
theorem lowerShriekPresheafStalkIso_hom :
    (lowerShriekPresheafStalkIso f ybar).hom =
      lowerShriekPresheafStalkComparison f ybar :=
  rfl

/-- The inverse map of `lowerShriekPresheafStalkIso` is the coproduct of stalk
maps from Lemma 37.41.3 neighbourhoods. -/
theorem lowerShriekPresheafStalkIso_inv :
    (lowerShriekPresheafStalkIso f ybar).inv =
      lowerShriekPresheafStalkComparisonInv f ybar :=
  rfl

end AlgebraicGeometry.Scheme.Etale

end
