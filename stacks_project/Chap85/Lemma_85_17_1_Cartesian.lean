/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Sheafification
public import stacks_project.Chap85.Definition_85_12_1_Fiberwise
public import stacks_project.Chap85.Lemma_85_16_1_Localization

/-!
# Cartesian sheaves on a fiberwise total site

A sheaf on the Grothendieck total site of a fiberwise simplicial site is cartesian when every
simplex-operator comparison `F(φ) : f_φ⁻¹ F_m ⟶ F_n` is an isomorphism. This is the case-B
owner for Situation 85.3.3, specialized to `(C / K)_total`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Functor

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck.Sheaf

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [h_fiberwise : HasSheafTransitions F J]
include h_fiberwise
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable (A : Type (w + 1)) [Category.{w} A]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck A]
variable [HasWeakSheafify (topology F J) A]

/-- The presheaf transition obtained by restricting along `ιNatTrans`.
Precomposition along a case-B structure map need not preserve sheaves, so this
map is constructed before applying the sheafification adjunction. -/
def transitionDirect {m n : SimplexCategory} (φ : m ⟶ n) (G : Sheaf (topology F J) A) :
    (F.map φ.op).toFunctor.op ⋙ ((component F J A m).obj G).obj ⟶
      ((component F J A n).obj G).obj :=
  whiskerRight (NatTrans.op (ιNatTrans φ.op)) G.obj

/-- Inverse image `f_φ⁻¹` of sheaves with coefficients in `A` along a simplex operator. -/
def sheafInverseImage {m n : SimplexCategory} (φ : m ⟶ n) :
    Sheaf ((J (op m)).toGrothendieck) A ⥤ Sheaf ((J (op n)).toGrothendieck) A :=
  (F.map φ.op).toFunctor.sheafPullbackCocontinuous A
    (J (op n)).toGrothendieck (J (op m)).toGrothendieck

/-- `sheafInverseImage` is cocontinuous sheaf pullback along `u_φ`. -/
theorem sheafInverseImage_eq {m n : SimplexCategory} (φ : m ⟶ n) :
    sheafInverseImage F J A φ =
      (F.map φ.op).toFunctor.sheafPullbackCocontinuous A
        (J (op n)).toGrothendieck (J (op m)).toGrothendieck :=
  sorry

/-- The comparison `F(φ) : f_φ⁻¹ F_m ⟶ F_n`, the sheafification mate of `transitionDirect`. -/
def sheafTransition {m n : SimplexCategory} (φ : m ⟶ n) (G : Sheaf (topology F J) A) :
    (sheafInverseImage F J A φ).obj ((component F J A m).obj G) ⟶
      (component F J A n).obj G :=
  ((sheafificationAdjunction ((J (op n)).toGrothendieck) A).homEquiv
      ((F.map φ.op).toFunctor.op ⋙ ((component F J A m).obj G).obj)
      ((component F J A n).obj G)).symm
    (transitionDirect F J A φ G)

/-- The sheafification mate of `sheafTransition` recovers the underlying map of
`transitionDirect`. -/
theorem sheafTransition_homEquiv {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf (topology F J) A) :
    ((sheafificationAdjunction ((J (op n)).toGrothendieck) A).homEquiv
        ((F.map φ.op).toFunctor.op ⋙ ((component F J A m).obj G).obj)
        ((component F J A n).obj G))
      (sheafTransition F J A φ G) =
    transitionDirect F J A φ G :=
  sorry

/-- A sheaf on the fiberwise total site is cartesian when `F(φ) : f_φ⁻¹ F_m ⟶ F_n` is an
isomorphism for every simplex operator `φ`. -/
class IsCartesian (G : Sheaf (topology F J) A) : Prop where
  /-- Every simplex-operator comparison `F(φ)` is an isomorphism. -/
  isIso_transition : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    IsIso (sheafTransition F J A φ G)

/-- Cartesianness is equivalent to every `F(φ)` being an isomorphism. -/
theorem isCartesian_iff (G : Sheaf (topology F J) A) :
    IsCartesian F J A G ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (sheafTransition F J A φ G) :=
  sorry

/-- A sheaf whose every simplex-operator comparison is an isomorphism is cartesian. -/
instance instIsCartesian_of_isIso (G : Sheaf (topology F J) A)
    [h : ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (sheafTransition F J A φ G)] :
    IsCartesian F J A G where
  isIso_transition := h

/-- Every simplex-operator comparison of a cartesian sheaf is an isomorphism. -/
instance instIsIso_sheafTransition (G : Sheaf (topology F J) A) [IsCartesian F J A G]
    {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso (sheafTransition F J A φ G) :=
  IsCartesian.isIso_transition φ

/-- The isomorphism `F(φ) : f_φ⁻¹ F_m ≅ F_n` attached to a cartesian sheaf. -/
def transitionIso (G : Sheaf (topology F J) A) [IsCartesian F J A G]
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (sheafInverseImage F J A φ).obj ((component F J A m).obj G) ≅
      (component F J A n).obj G :=
  asIso (sheafTransition F J A φ G)

/-- The forward map of `transitionIso` is `sheafTransition`. -/
theorem transitionIso_hom (G : Sheaf (topology F J) A) [IsCartesian F J A G]
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (transitionIso F J A G φ).hom = sheafTransition F J A φ G :=
  sorry

/-- The object property of being a cartesian sheaf on the fiberwise total site. -/
abbrev cartesianProperty : ObjectProperty (Sheaf (topology F J) A) :=
  fun G ↦ IsCartesian F J A G

/-- The category of cartesian sheaves on the fiberwise total site. -/
abbrev Cartesian := (cartesianProperty F J A).FullSubcategory

/-- The underlying sheaf of an object of `Cartesian` is cartesian. -/
theorem cartesian_isCartesian (G : Cartesian F J A) : IsCartesian F J A G.obj :=
  sorry

end CategoryTheory.Grothendieck.Sheaf

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (K : SimplicialObject (FormalCoproduct.{w} C))
variable (A : Type (max w u v + 1)) [Category.{max w u v} A]
variable [HasWeakSheafify J A]
variable [HasWeakSheafify (overSiteTotalTopology J K) A]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify (overSitePrecoverage J K n).toGrothendieck A]
variable [∀ n : SimplexCategoryᵒᵖ,
    HasWeakSheafify (overSitePrecoverage J K n).toGrothendieck (Type (max w u v))]
variable [HasWeakSheafify (overSiteTotalTopology J K) (Type (max w u v))]

/-- A sheaf on `(C / K)_total` is cartesian when every simplex-operator comparison
`F(φ) : f_φ⁻¹ F_m ⟶ F_n` is an isomorphism. -/
abbrev IsCartesian (G : Sheaf (overSiteTotalTopology J K) A) : Prop :=
  Grothendieck.Sheaf.IsCartesian (overSiteDiagram K) (overSitePrecoverage J K) A G

/-- Cartesianness on `(C / K)_total` is equivalent to every `F(φ)` being an isomorphism. -/
theorem isCartesian_iff (G : Sheaf (overSiteTotalTopology J K) A) :
    IsCartesian J K A G ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n),
        IsIso (Grothendieck.Sheaf.sheafTransition
          (overSiteDiagram K) (overSitePrecoverage J K) A φ G) :=
  sorry

/-- The object property of being a cartesian sheaf on `(C / K)_total`. -/
abbrev cartesianProperty : ObjectProperty (Sheaf (overSiteTotalTopology J K) A) :=
  Grothendieck.Sheaf.cartesianProperty (overSiteDiagram K) (overSitePrecoverage J K) A

/-- The category of cartesian sheaves on `(C / K)_total`. -/
abbrev Cartesian :=
  Grothendieck.Sheaf.Cartesian (overSiteDiagram K) (overSitePrecoverage J K) A

/-- The underlying sheaf of an object of `Cartesian` is cartesian. -/
theorem cartesian_isCartesian (G : Cartesian J K A) : IsCartesian J K A G.obj :=
  sorry

/-- Inverse image `a⁻¹` along `j_total` of a sheaf on `C`. -/
abbrev inverseImage : Sheaf J A ⥤ Sheaf (overSiteTotalTopology J K) A :=
  (totalForget K).sheafPushforwardContinuous A (overSiteTotalTopology J K) J

/-- `inverseImage` is continuous sheaf pushforward of `j_total`. -/
theorem inverseImage_eq :
    inverseImage J K A =
      (totalForget K).sheafPushforwardContinuous A (overSiteTotalTopology J K) J :=
  sorry

variable [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ A,
    (totalForget K).op.HasPointwiseRightKanExtension P]

/-- Direct image `a_*` along `j_total` of a sheaf on `(C / K)_total`. -/
abbrev directImage : Sheaf (overSiteTotalTopology J K) A ⥤ Sheaf J A :=
  (totalForget K).sheafPushforwardCocontinuous A (overSiteTotalTopology J K) J

/-- `directImage` is cocontinuous sheaf pushforward of `j_total`. -/
theorem directImage_eq :
    directImage J K A =
      (totalForget K).sheafPushforwardCocontinuous A (overSiteTotalTopology J K) J :=
  sorry

/-- Inverse image `a⁻¹ F` of a sheaf on `C` is cartesian on `(C / K)_total`. -/
instance inverseImage_isCartesian (F : Sheaf J A) :
    IsCartesian J K A ((inverseImage J K A).obj F) :=
  sorry

end CategoryTheory.SemiRepresentableFamily
