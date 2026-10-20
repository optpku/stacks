module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.Abelian
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.Morphism

/-! # Abelian cocontinuous pushforward and its right derived functors -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]

/-- Pointwise right Kan extensions along `(lisseEtaleMap f).op` exist on abelian
presheaves. -/
instance lisseEtaleMap.instHasPointwiseRightKanExtension (f : X ⟶ Y) [Smooth f]
    (P : (lisseEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (lisseEtaleMap f).op.HasPointwiseRightKanExtension P :=
  sorry

/-- Pointwise right Kan extensions along `(flatFppfMap f).op` exist on abelian
presheaves. -/
instance flatFppfMap.instHasPointwiseRightKanExtension (f : X ⟶ Y) [Flat f]
    (P : (flatFppfSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    (flatFppfMap f).op.HasPointwiseRightKanExtension P :=
  sorry

/-- The underived pushforward `f'_*` on abelian sheaves for a smooth morphism of
lisse-étale sites. -/
abbrev lisseEtalePushforward (f : X ⟶ Y) [Smooth f] :
    Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (lisseEtaleTopology Y) AddCommGrpCat.{u + 1} :=
  (lisseEtaleMap f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
    (lisseEtaleTopology X) (lisseEtaleTopology Y)

/-- Cocontinuous lisse-étale pushforward of abelian sheaves is additive. -/
instance lisseEtalePushforward.instAdditive (f : X ⟶ Y) [Smooth f] :
    (lisseEtalePushforward f).Additive :=
  sorry

/-- The underived pushforward `f'_*` on abelian sheaves for a flat morphism of
flat-fppf sites. -/
abbrev flatFppfPushforward (f : X ⟶ Y) [Flat f] :
    Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (flatFppfTopology Y) AddCommGrpCat.{u + 1} :=
  (flatFppfMap f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
    (flatFppfTopology X) (flatFppfTopology Y)

/-- Cocontinuous flat-fppf pushforward of abelian sheaves is additive. -/
instance flatFppfPushforward.instAdditive (f : X ⟶ Y) [Flat f] :
    (flatFppfPushforward f).Additive :=
  sorry

variable [HasSheafify (lisseEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (lisseEtaleTopology Y) AddCommGrpCat.{u + 1}]
variable [HasInjectiveResolutions
    (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1})]

/-- The degree-`p` higher direct image `R^p f'_* H` of an abelian sheaf on the
lisse-étale site along a smooth morphism. -/
abbrev lisseEtaleHigherDirectImage (f : X ⟶ Y) [Smooth f]
    (H : Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1}) (p : ℕ) :
    Sheaf (lisseEtaleTopology Y) AddCommGrpCat.{u + 1} :=
  ((lisseEtalePushforward f).rightDerived p).obj H

variable [HasSheafify (flatFppfTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (flatFppfTopology Y) AddCommGrpCat.{u + 1}]
variable [HasInjectiveResolutions
    (Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1})]

/-- The degree-`p` higher direct image `R^p f'_* H` of an abelian sheaf on the
flat-fppf site along a flat morphism. -/
abbrev flatFppfHigherDirectImage (f : X ⟶ Y) [Flat f]
    (H : Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1}) (p : ℕ) :
    Sheaf (flatFppfTopology Y) AddCommGrpCat.{u + 1} :=
  ((flatFppfPushforward f).rightDerived p).obj H

end AlgebraicGeometry.AlgebraicStack
