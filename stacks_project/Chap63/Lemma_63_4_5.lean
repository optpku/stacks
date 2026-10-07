module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import stacks_project.Chap63.Definition_63_4_4_LowerShriek
public import stacks_project.Chap63.Lemma_63_4_2

/-!
# Stalk formula, exactness, and coproducts for compact-support direct image

Lemma 63.4.5: for a locally quasi-finite morphism `f : X ⟶ Y`, the functor
`f_!` on abelian étale sheaves has stalks `(f_! F)_ȳ ≅ ⊕_{f(x̄)=ȳ} F_x̄`,
and is exact and commutes with direct sums.
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
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/-- Lemma 63.4.5 (1): Let `f : X ⟶ Y` be a locally quasi-finite morphism of
schemes. For `F` in `Ab(X_étale)` and a geometric point `ȳ : Spec k ⟶ Y`,
there is a canonical identification `(f_! F)_ȳ ≅ ⊕_{f(x̄)=ȳ} F_x̄`, functorial
in `F`. Stacks locally quasi-finite is rendered as `[LocallyQuasiFinite f]`
together with `[LocallyOfFiniteType f]`. -/
@[stacks 0F5F]
def lowerShriekStalkIso (ybar : GeometricPoint Y) :
    lowerShriek f ⋙ (toSmallEtalePoint ybar).sheafFiber ≅
      abelianStalkCoproduct f ybar :=
  Functor.isoWhiskerLeft (lowerShriekPresheaf f)
      ((toSmallEtalePoint ybar).presheafToSheafCompSheafFiberIso AddCommGrpCat.{u}) ≪≫
    lowerShriekPresheafStalkIso f ybar

/-- The identification of `lowerShriekStalkIso` at an abelian étale sheaf `F`. -/
def lowerShriekStalkIso_app (ybar : GeometricPoint Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (toSmallEtalePoint ybar).sheafFiber.obj ((lowerShriek f).obj F) ≅
      (abelianStalkCoproduct f ybar).obj F :=
  (lowerShriekStalkIso f ybar).app F

/-- Lemma 63.4.5 (2): Let `f : X ⟶ Y` be a locally quasi-finite morphism of
schemes. The functor `f_! : Ab(X_étale) ⥤ Ab(Y_étale)` is exact. -/
@[stacks 0F5F]
theorem lowerShriek_exact :
    exactFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (lowerShriek f) :=
  sorry

/-- Compact-support direct image along a locally quasi-finite morphism preserves
finite limits. -/
instance lowerShriek_preservesFiniteLimits :
    PreservesFiniteLimits (lowerShriek f) :=
  sorry

/-- Compact-support direct image along a locally quasi-finite morphism preserves
finite colimits. -/
instance lowerShriek_preservesFiniteColimits :
    PreservesFiniteColimits (lowerShriek f) :=
  sorry

/-- Lemma 63.4.5 (3): Let `f : X ⟶ Y` be a locally quasi-finite morphism of
schemes. The functor `f_! : Ab(X_étale) ⥤ Ab(Y_étale)` commutes with direct
sums. -/
@[stacks 0F5F, instance]
instance lowerShriek_preservesCoproducts {I : Type u} :
    PreservesColimitsOfShape (Discrete I) (lowerShriek f) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
