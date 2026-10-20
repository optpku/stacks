/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.Stalk

/-!
# Stalk formula, exactness, and coproducts for compact-support direct image

For a locally quasi-finite morphism `f : X ⟶ Y`, the functor
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

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
  [LocallyOfFiniteType f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/-- Compact-support direct image along a locally quasi-finite morphism has
stalks naturally isomorphic to the coproduct of the abelian étale stalks at
same-field geometric lifts. -/
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

/-- Compact-support direct image of abelian étale sheaves along a locally
quasi-finite morphism is exact. -/
@[stacks 0F5F]
theorem lowerShriek_exact :
    exactFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (lowerShriek f) :=
  sorry

end

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/-- Compact-support direct image along a locally quasi-finite morphism preserves
finite limits. -/
instance lowerShriek_preservesFiniteLimits [LocallyOfFiniteType f] :
    PreservesFiniteLimits (lowerShriek f) :=
  sorry

/-- Compact-support direct image along a locally quasi-finite morphism preserves
finite colimits. -/
instance lowerShriek_preservesFiniteColimits [LocallyOfFiniteType f] :
    PreservesFiniteColimits (lowerShriek f) :=
  sorry

/-- Compact-support direct image of abelian étale sheaves along a locally
quasi-finite morphism preserves arbitrary coproducts. -/
@[stacks 0F5F, instance]
instance lowerShriek_preservesCoproducts [LocallyOfFiniteType f] {I : Type u} :
    PreservesColimitsOfShape (Discrete I) (lowerShriek f) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
