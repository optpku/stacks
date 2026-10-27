/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.CategoryTheory.Sites.Grothendieck.LowerShriek
public import ReasLib.CategoryTheory.Sites.Grothendieck.SimplicialDerivedMorphism
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition

/-!
# Cartesian objects on a fiberwise simplicial site

Sheafified restriction comparisons and their unbounded derived counterparts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [h_fiberwise : HasSheafTransitions F J]
include h_fiberwise
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]

/-- Fiber inclusion `ι F (op n)` is continuous for the fiberwise total topology. -/
instance ι_isContinuous (n : SimplexCategory) :
    (ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J) :=
  h_fiberwise.component_continuous n

/-- Fiber inclusion `ι F (op n)` is cocontinuous for the fiberwise total topology. -/
instance ι_isCocontinuous (n : SimplexCategory) :
    (ι F (op n)).IsCocontinuous (J (op n)).toGrothendieck (topology F J) :=
  h_fiberwise.component_cocontinuous n

namespace Sheaf

variable (A : Type (w + 1)) [Category.{w} A]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck A]
variable [HasWeakSheafify (topology F J) A]

/-- The presheaf transition obtained by restricting along `ιNatTrans`.
Precomposition along a case-B structure map need not preserve sheaves, so this
map is constructed before applying the sheafification adjunction. -/
def transitionDirect {m n : SimplexCategory} (φ : m ⟶ n) (G : Sheaf (topology F J) A) :
    (F.map φ.op).toFunctor.op ⋙ ((fiberRestrict F J A m).obj G).obj ⟶
      ((fiberRestrict F J A n).obj G).obj :=
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
  rfl

/-- The comparison `F(φ) : f_φ⁻¹ F_m ⟶ F_n`, the sheafification mate of `transitionDirect`. -/
def sheafTransition {m n : SimplexCategory} (φ : m ⟶ n) (G : Sheaf (topology F J) A) :
    (sheafInverseImage F J A φ).obj ((fiberRestrict F J A m).obj G) ⟶
      (fiberRestrict F J A n).obj G :=
  ((sheafificationAdjunction ((J (op n)).toGrothendieck) A).homEquiv
      ((F.map φ.op).toFunctor.op ⋙ ((fiberRestrict F J A m).obj G).obj)
      ((fiberRestrict F J A n).obj G)).symm
    (transitionDirect F J A φ G)

/-- The sheafification mate of `sheafTransition` recovers the underlying map of
`transitionDirect`. -/
theorem sheafTransition_homEquiv {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf (topology F J) A) :
    ((sheafificationAdjunction ((J (op n)).toGrothendieck) A).homEquiv
        ((F.map φ.op).toFunctor.op ⋙ ((fiberRestrict F J A m).obj G).obj)
        ((fiberRestrict F J A n).obj G))
      (sheafTransition F J A φ G) =
    transitionDirect F J A φ G :=
  Equiv.apply_symm_apply _ _

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
  ⟨fun h ↦ h.isIso_transition, fun h ↦ ⟨h⟩⟩

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
    (sheafInverseImage F J A φ).obj ((fiberRestrict F J A m).obj G) ≅
      (fiberRestrict F J A n).obj G :=
  asIso (sheafTransition F J A φ G)

/-- The forward map of `transitionIso` is `sheafTransition`. -/
theorem transitionIso_hom (G : Sheaf (topology F J) A) [IsCartesian F J A G]
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (transitionIso F J A G φ).hom = sheafTransition F J A φ G :=
  rfl

/-- The object property of being a cartesian sheaf on the fiberwise total site. -/
abbrev cartesianProperty : ObjectProperty (Sheaf (topology F J) A) :=
  fun G ↦ IsCartesian F J A G

/-- The category of cartesian sheaves on the fiberwise total site. -/
abbrev Cartesian := (cartesianProperty F J A).FullSubcategory

/-- The underlying sheaf of an object of `Cartesian` is cartesian. -/
theorem cartesian_isCartesian (G : Cartesian F J A) : IsCartesian F J A G.obj :=
  G.property

/-- The sheafified fiber restriction comparison is natural in the total sheaf. -/
theorem sheafTransition_naturality {m n : SimplexCategory} (φ : m ⟶ n)
    {G H : Sheaf (topology F J) A} (f : G ⟶ H) :
    (fiberRestrict F J A m ⋙ sheafInverseImage F J A φ).map f ≫
        sheafTransition F J A φ H =
      sheafTransition F J A φ G ≫ (fiberRestrict F J A n).map f :=
  sorry

end Sheaf

variable [IsFiberwiseSite F J]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]

/-- Abelian cocontinuous inverse image is additive and preserves finite limits and colimits. -/
theorem abelianInverseImage_exact {m n : SimplexCategory} (φ : m ⟶ n) :
    (Sheaf.sheafInverseImage F J AddCommGrpCat.{w} φ).Additive ∧
      PreservesFiniteLimits (Sheaf.sheafInverseImage F J AddCommGrpCat.{w} φ) ∧
      PreservesFiniteColimits (Sheaf.sheafInverseImage F J AddCommGrpCat.{w} φ) :=
  sorry

/-- The exact inverse-image functor on abelian sheaves along a simplex operator. -/
def abelianInverseImageExact {m n : SimplexCategory} (φ : m ⟶ n) :
    Sheaf ((J (op m)).toGrothendieck) AddCommGrpCat.{w} ⥤ₑ
      Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w} :=
  { obj := Sheaf.sheafInverseImage F J AddCommGrpCat.{w} φ
    property := ⟨(abelianInverseImage_exact F J φ).2.1,
      (abelianInverseImage_exact F J φ).2.2⟩ }

/-- The abelian sheaf comparison as a natural transformation. -/
def abelianTransitionNatTrans {m n : SimplexCategory} (φ : m ⟶ n) :
    fiberRestrict F J AddCommGrpCat.{w} m ⋙ (abelianInverseImageExact F J φ).obj ⟶
      fiberRestrict F J AddCommGrpCat.{w} n where
  app G := Sheaf.sheafTransition F J AddCommGrpCat.{w} φ G
  naturality _ _ f := Sheaf.sheafTransition_naturality F J AddCommGrpCat.{w} φ f

/-- Bundled exact restriction of abelian sheaves to a fiber. -/
def derivedComponentExact (n : SimplexCategory) :
    Sheaf (topology F J) AddCommGrpCat.{w} ⥤ₑ
      Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w} :=
  ExactFunctor.of (fiberRestrict F J AddCommGrpCat.{w} n)

/-- Localization of the abelian restriction comparison after exact functor composition. -/
def derivedTransition {m n : SimplexCategory} (φ : m ⟶ n)
    (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})) :
    (abelianInverseImageExact F J φ).mapDerivedCategory.obj
        ((derivedRestrict F J m).obj K) ⟶ (derivedRestrict F J n).obj K :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
      (derivedComponentExact F J m) (abelianInverseImageExact F J φ)).inv.app K ≫
    (ExactFunctor.MapDerivedCategory.map
      (F := (derivedComponentExact F J m).comp (abelianInverseImageExact F J φ))
      (G := derivedComponentExact F J n)
      (ObjectProperty.homMk (abelianTransitionNatTrans F J φ))).app K

namespace AbelianDerived

/-- An object of `D(C_total)` is cartesian when `f_φ⁻¹ K_m ⟶ K_n` is an isomorphism for
every simplex operator `φ`. -/
class IsCartesian
    (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})) : Prop where
  /-- Every simplex-operator derived comparison is an isomorphism. -/
  isIso_transition : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    IsIso (derivedTransition F J φ K)

/-- Cartesianness of an object of `D(C_total)` is equivalent to every simplex-operator
comparison being an isomorphism. -/
theorem isCartesian_iff
    (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})) :
    IsCartesian F J K ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (derivedTransition F J φ K) :=
  ⟨fun h ↦ h.isIso_transition, fun h ↦ ⟨h⟩⟩

/-- An object of `D(C_total)` whose every simplex-operator comparison is an isomorphism
is cartesian. -/
instance instIsCartesian_of_isIso
    (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
    [h : ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (derivedTransition F J φ K)] :
    IsCartesian F J K where
  isIso_transition := h

/-- Every simplex-operator comparison of a cartesian object of `D(C_total)` is an
isomorphism. -/
instance instIsIso_derivedTransition
    (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
    [IsCartesian F J K] {m n : SimplexCategory} (φ : m ⟶ n) :
    IsIso (derivedTransition F J φ K) :=
  IsCartesian.isIso_transition φ

/-- The isomorphism `f_φ⁻¹ K_m ≅ K_n` attached to a cartesian object of `D(C_total)`. -/
def transitionIso (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
    [IsCartesian F J K] {m n : SimplexCategory} (φ : m ⟶ n) :
    (abelianInverseImageExact F J φ).mapDerivedCategory.obj ((derivedRestrict F J m).obj K) ≅
      (derivedRestrict F J n).obj K :=
  asIso (derivedTransition F J φ K)

/-- The forward map of `AbelianDerived.transitionIso` is `derivedTransition`. -/
theorem transitionIso_hom
    (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))
    [IsCartesian F J K] {m n : SimplexCategory} (φ : m ⟶ n) :
    (transitionIso F J K φ).hom = derivedTransition F J φ K :=
  rfl

end AbelianDerived

end CategoryTheory.Grothendieck
