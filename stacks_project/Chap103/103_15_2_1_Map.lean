/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.Abelian
public import stacks_project.Chap103.«103_15_1_1_Map»

/-!
# Cocontinuous higher direct images on lisse-étale and flat-fppf sites

The underived pushforward `f'_*` is the cocontinuous sheaf pushforward of the
restricted site functor from `103_15_1_1_Map`. Higher direct images are the
right derived functors of that pushforward on abelian sheaves.
-/

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

/-- `lisseEtalePushforward f` is the cocontinuous sheaf pushforward of
`lisseEtaleMap f`. -/
theorem lisseEtalePushforward_eq (f : X ⟶ Y) [Smooth f] :
    lisseEtalePushforward f =
      (lisseEtaleMap f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (lisseEtaleTopology X) (lisseEtaleTopology Y) :=
  sorry

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

/-- `flatFppfPushforward f` is the cocontinuous sheaf pushforward of
`flatFppfMap f`. -/
theorem flatFppfPushforward_eq (f : X ⟶ Y) [Flat f] :
    flatFppfPushforward f =
      (flatFppfMap f).sheafPushforwardCocontinuous AddCommGrpCat.{u + 1}
        (flatFppfTopology X) (flatFppfTopology Y) :=
  sorry

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

/-- `lisseEtaleHigherDirectImage f H p` is the degree-`p` right derived functor
of `lisseEtalePushforward f` evaluated at `H`. -/
theorem lisseEtaleHigherDirectImage_eq (f : X ⟶ Y) [Smooth f]
    (H : Sheaf (lisseEtaleTopology X) AddCommGrpCat.{u + 1}) (p : ℕ) :
    lisseEtaleHigherDirectImage f H p =
      ((lisseEtalePushforward f).rightDerived p).obj H :=
  sorry

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

/-- `flatFppfHigherDirectImage f H p` is the degree-`p` right derived functor of
`flatFppfPushforward f` evaluated at `H`. -/
theorem flatFppfHigherDirectImage_eq (f : X ⟶ Y) [Flat f]
    (H : Sheaf (flatFppfTopology X) AddCommGrpCat.{u + 1}) (p : ℕ) :
    flatFppfHigherDirectImage f H p =
      ((flatFppfPushforward f).rightDerived p).obj H :=
  sorry

end AlgebraicGeometry.AlgebraicStack
