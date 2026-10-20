module

public import ReasLib.CategoryTheory.Sites.Topos.Morphism
public import ReasLib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cocontinuous functors of sites

This file owns the sheaf-theoretic functors and the induced morphism of topoi
attached to a cocontinuous functor of sites.  The coefficient-generic
pullback is separated from the set-valued adjunction and exactness API,
because the latter uses the canonical right-Kan-extension description of
cocontinuous pushforward.

## Main declarations

- `Functor.sheafPullbackCocontinuous` is the coefficient-generic sheafified
  pullback.
- `Functor.sheafPullbackCocontinuousAdjunction` and
  `Functor.sheafPullbackCocontinuous_exact` give its set-valued adjunction
  and exactness properties.
- `Functor.morphismOfTopoiInOfCocontinuous` packages the resulting geometric
  morphism.
-/

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- The coefficient-generic pullback of sheaves along a cocontinuous functor:
forget to presheaves, precompose along the opposite functor, and sheafify. -/
def sheafPullbackCocontinuous
    (G : C ⥤ D)
    (A : Type (w + 1)) [Category.{w} A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasWeakSheafify J A] :
    Sheaf K A ⥤ Sheaf J A :=
  sheafToPresheaf K A ⋙
    (whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op ⋙
    presheafToSheaf J A

section ContinuousCocontinuous

variable (G : C ⥤ D)
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
variable [G.IsContinuous J K] [G.IsCocontinuous J K]
variable [∀ F : Cᵒᵖ ⥤ Type w, G.op.HasPointwiseRightKanExtension F]

/-- The component of the comparison from cocontinuous pullback to continuous
pushforward for a functor of sites which has both properties. -/
noncomputable def CocontinuousPullback.comparisonApp
    (F : Sheaf K (Type w)) :
    (G.sheafPullbackCocontinuous (Type w) J K).obj F ⟶
      (G.sheafPushforwardContinuous (Type w) J K).obj F :=
  (G.pushforwardContinuousSheafificationCompatibility (Type w) J K).hom.app F.obj ≫
    (G.sheafPushforwardContinuous (Type w) J K).map (sheafificationIso F).inv

/-- The cocontinuous-to-continuous comparison components are natural in the
input sheaf. -/
theorem CocontinuousPullback.comparisonApp_naturality
    {F F' : Sheaf K (Type w)} (η : F ⟶ F') :
    (G.sheafPullbackCocontinuous (Type w) J K).map η ≫
        CocontinuousPullback.comparisonApp G J K F' =
      CocontinuousPullback.comparisonApp G J K F ≫
        (G.sheafPushforwardContinuous (Type w) J K).map η := sorry

/-- The natural comparison from cocontinuous sheaf pullback to continuous
sheaf pushforward. -/
@[stacks 06NW "cocontinuous-to-continuous comparison"]
noncomputable def CocontinuousPullback.comparison :
    G.sheafPullbackCocontinuous (Type w) J K ⟶
      G.sheafPushforwardContinuous (Type w) J K :=
  NatTrans.mk
    (fun F ↦ CocontinuousPullback.comparisonApp G J K F)
    (fun {_ _} η ↦
      CocontinuousPullback.comparisonApp_naturality G J K η)

/-- The isomorphism from cocontinuous pullback to continuous pushforward is the
sheafification compatibility isomorphism followed by the inverse of the
pushforward of the sheafification isomorphism. -/
@[stacks 06NW "actual cocontinuous-to-continuous comparison"]
noncomputable def CocontinuousPullback.comparisonIso :
    G.sheafPullbackCocontinuous (Type w) J K ≅
      G.sheafPushforwardContinuous (Type w) J K :=
  NatIso.ofComponents
    (fun F =>
      (G.pushforwardContinuousSheafificationCompatibility (Type w) J K).app F.obj ≪≫
        ((G.sheafPushforwardContinuous (Type w) J K).mapIso (sheafificationIso F)).symm)
    (fun {_ _} η ↦ CocontinuousPullback.comparisonApp_naturality G J K η)

/-- The actual isomorphism's forward transformation is the canonical comparison. -/
@[simp]
theorem CocontinuousPullback.comparisonIso_hom :
    (CocontinuousPullback.comparisonIso G J K).hom =
      CocontinuousPullback.comparison G J K :=
  rfl

/-- The canonical comparison from cocontinuous pullback to continuous
pushforward is invertible. -/
@[stacks 06NW "invertibility of the cocontinuous-to-continuous comparison"]
instance CocontinuousPullback.comparison.isIso :
    IsIso (CocontinuousPullback.comparison G J K) :=
  (CocontinuousPullback.comparisonIso G J K).isIso_hom

/-- An explicit isomorphism presentation of the canonical cocontinuous-to-continuous
comparison.  The equality field is part of the presentation, so downstream constructions can
use the inverse data without carrying an unrelated proof argument alongside the isomorphism. -/
@[stacks 06NW "explicit cocontinuous-to-continuous comparison"]
structure CocontinuousPullback.ComparisonIso where
  /-- The displayed isomorphism between the two sheaf functors. -/
  iso : G.sheafPullbackCocontinuous (Type w) J K ≅
    G.sheafPushforwardContinuous (Type w) J K
  /-- The forward map is the canonical comparison. -/
  hom_eq : iso.hom = CocontinuousPullback.comparison G J K

/-- Package an isomorphism and a proof that its forward map is the canonical comparison. -/
def CocontinuousPullback.ComparisonIso.ofIso
    (e : G.sheafPullbackCocontinuous (Type w) J K ≅
      G.sheafPushforwardContinuous (Type w) J K)
    (h : e.hom = CocontinuousPullback.comparison G J K) :
    CocontinuousPullback.ComparisonIso G J K :=
  ⟨e, h⟩

/-- Explicit presentations of the canonical cocontinuous-to-continuous comparison are unique. -/
theorem CocontinuousPullback.ComparisonIso.eq
    (e e' : CocontinuousPullback.ComparisonIso G J K) : e = e' := sorry

/- The structure is a proof-carrying presentation of the canonical comparison.  Its fields and
   the two small constructors are tagged separately so consumers can find the exact data/spec
   boundary without searching through the parent comparison declaration. -/
attribute [stacks 06NW "cocontinuous comparison isomorphism field"]
  CocontinuousPullback.ComparisonIso.iso
attribute [stacks 06NW "cocontinuous comparison specification field"]
  CocontinuousPullback.ComparisonIso.hom_eq
attribute [stacks 06NW "cocontinuous comparison isomorphism constructor"]
  CocontinuousPullback.ComparisonIso.ofIso
attribute [stacks 06NW "cocontinuous comparison presentation uniqueness"]
  CocontinuousPullback.ComparisonIso.eq

end ContinuousCocontinuous

section ContinuousCocontinuousEpimorphisms

variable {G : C ⥤ D}
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable [G.IsContinuous J K]

namespace SheafPushforwardContinuous

/-- Continuous direct image along a cocontinuous functor of sites preserves
locally surjective morphisms of `Type`-valued sheaves.  The generic mapped
morphism instance is supplied by `Functor.PreservesLocallySurjective`. -/
instance preservesLocallySurjective
    [G.IsCocontinuous J K] :
    (G.sheafPushforwardContinuous (Type w) J K).PreservesLocallySurjective := sorry

/-- Continuous direct image along a cocontinuous functor of sites preserves epimorphisms of
`Type`-valued sheaves whenever local surjectivity detects epimorphisms in the input sheaf
category. -/
instance preservesEpimorphisms
    [G.IsCocontinuous J K] [HasSheafify K (Type w)] :
    (G.sheafPushforwardContinuous (Type w) J K).PreservesEpimorphisms := sorry

end SheafPushforwardContinuous

end ContinuousCocontinuousEpimorphisms

section Cocontinuous

variable (G : C ⥤ D)
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [G.IsCocontinuous J K]
variable [∀ F : Cᵒᵖ ⥤ Type w, G.op.HasPointwiseRightKanExtension F]

/-- The set-valued cocontinuous sheaf pullback is left adjoint to the
cocontinuous sheaf pushforward. -/
noncomputable def sheafPullbackCocontinuousAdjunction
    [HasWeakSheafify J (Type w)] :
    G.sheafPullbackCocontinuous (Type w) J K ⊣ G.sheafPushforwardCocontinuous (Type w) J K :=
  ((G.op.ranAdjunction (Type w)).comp (sheafificationAdjunction J (Type w))).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf K (Type w)) (Functor.FullyFaithful.id _)
    (Iso.refl _)
    (G.sheafPushforwardCocontinuousCompSheafToPresheafIso (Type w) J K).symm

/-- The set-valued cocontinuous sheaf pullback preserves finite limits and
finite colimits. -/
theorem sheafPullbackCocontinuous_exact
    [HasSheafify J (Type w)] :
    exactFunctor (Sheaf K (Type w)) (Sheaf J (Type w))
      (G.sheafPullbackCocontinuous (Type w) J K) := sorry

/-- A cocontinuous functor of sites determines a morphism of topoi whose
inverse image is the sheafified pullback and whose direct image is the
cocontinuous sheaf pushforward. -/
def morphismOfTopoiInOfCocontinuous
    [HasSheafify J (Type w)] : MorphismOfTopoiIn K J where
  inverseImageFunctor :=
    (LeftExactFunctor.ofExact (Sheaf K (Type w)) (Sheaf J (Type w))).obj
      ⟨G.sheafPullbackCocontinuous (Type w) J K,
        G.sheafPullbackCocontinuous_exact J K⟩
  pushforward := G.sheafPushforwardCocontinuous (Type w) J K
  adjunction := G.sheafPullbackCocontinuousAdjunction J K

/-- The direct image of the cocontinuously induced morphism of topoi is the
cocontinuous sheaf pushforward. -/
@[simp] theorem morphismOfTopoiInOfCocontinuous_pushforward
    [HasSheafify J (Type w)] :
    (G.morphismOfTopoiInOfCocontinuous J K).pushforward =
      G.sheafPushforwardCocontinuous (Type w) J K := rfl

/-- The inverse image of the cocontinuously induced morphism of topoi is the
sheafified cocontinuous pullback. -/
@[simp] theorem morphismOfTopoiInOfCocontinuous_inverseImage
    [HasSheafify J (Type w)] :
    (G.morphismOfTopoiInOfCocontinuous J K).inverseImage =
      G.sheafPullbackCocontinuous (Type w) J K := rfl

/-- The adjunction stored by the cocontinuously induced morphism of topoi is
the canonical cocontinuous pullback-pushforward adjunction. -/
theorem morphismOfTopoiInOfCocontinuous_spec
    [HasSheafify J (Type w)] :
    (G.morphismOfTopoiInOfCocontinuous J K).adjunction =
      G.sheafPullbackCocontinuousAdjunction J K := rfl

end Cocontinuous

end CategoryTheory.Functor
