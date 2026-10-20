module

public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Functor
public import ReasLib.Algebra.Homology.HomotopyCategory.Injective.Functor
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Localizing Functorial Injective Resolutions

This leaf is independent of a particular derived-category model. It records
that a functorial bounded-below injective resolution inverts quasi-isomorphisms
and gives the resulting equivalence criterion for any localization at them.
-/

open CategoryTheory
open CategoryTheory.MorphismProperty

universe v₃ v₂ w u₂ v u

namespace CategoryTheory.HomotopyCategory.Plus.InjectiveResolutionFunctor

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- Stacks 05TK: a functorial bounded-below injective resolution sends
bounded-below quasi-isomorphisms to isomorphisms. -/
@[stacks 05TK]
theorem isInvertedBy (J : HomotopyCategory.Plus.InjectiveResolutionFunctor 𝒜) :
    (HomotopyCategory.Plus.quasiIso 𝒜).IsInvertedBy J.toFunctor := sorry

/-- Stacks 05TK: a factorization of a functorial bounded-below injective
resolution through any localization of `K⁺(𝒜)` at quasi-isomorphisms is an
equivalence. This is the model-independent form of the derived-category
lifting criterion. -/
@[stacks 05TK]
theorem lift_isEquivalence_of_isLocalization
    {D : Type w} [Category.{v₂} D]
    (Q : HomotopyCategory.Plus 𝒜 ⥤ D)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso 𝒜)]
    (J : HomotopyCategory.Plus.InjectiveResolutionFunctor 𝒜)
    (L : D ⥤ HomotopyCategory.Plus.Injective 𝒜)
    (fac : Q ⋙ L ≅ J.toFunctor) :
    Functor.IsEquivalence L := sorry

/-- Stacks 05TN: the comparison from a functor on bounded-below homotopy objects to its
evaluation on injective representatives obtained from a lift of a functorial injective
resolution.  This construction is independent of a particular derived-category model and of
any additive or triangulated structure on the target. -/
@[stacks 05TN]
noncomputable def liftComparison
    {D : Type w} [Category.{v₂} D] {E : Type u₂} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus 𝒜 ⥤ D)
    (J : HomotopyCategory.Plus.InjectiveResolutionFunctor 𝒜)
    (L : D ⥤ HomotopyCategory.Plus.Injective 𝒜)
    (hL : Localization.Lifting Q (HomotopyCategory.Plus.quasiIso 𝒜) J.toFunctor L)
    (G : HomotopyCategory.Plus 𝒜 ⥤ E) :
    G ⟶ Q ⋙ L ⋙ HomotopyCategory.Plus.Injective.ι 𝒜 ⋙ G :=
  Functor.whiskerRight J.ι G ≫
    (Functor.associator J.toFunctor (HomotopyCategory.Plus.Injective.ι 𝒜) G).hom ≫
      (Functor.isoWhiskerRight hL.iso.symm
        (HomotopyCategory.Plus.Injective.ι 𝒜 ⋙ G)).hom ≫
        (Functor.associator Q L (HomotopyCategory.Plus.Injective.ι 𝒜 ⋙ G)).hom

/-- Stacks 05TN: a lift of a functorial bounded-below injective resolution through any
localization at quasi-isomorphisms computes the right derived functor of every functor out of
the bounded-below homotopy category.  The usual additive functor formulation is the
specialization `G = F.toBoundedBelowDerived`. -/
@[stacks 05TN]
theorem lift_comp_isRightDerivedFunctor
    {D : Type w} [Category.{v₂} D] {E : Type u₂} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus 𝒜 ⥤ D)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso 𝒜)]
    (J : HomotopyCategory.Plus.InjectiveResolutionFunctor 𝒜)
    (L : D ⥤ HomotopyCategory.Plus.Injective 𝒜)
    (hL : Localization.Lifting Q (HomotopyCategory.Plus.quasiIso 𝒜) J.toFunctor L)
    (G : HomotopyCategory.Plus 𝒜 ⥤ E) :
    (L ⋙ HomotopyCategory.Plus.Injective.ι 𝒜 ⋙ G).IsRightDerivedFunctor
      (J.liftComparison Q L hL G) (HomotopyCategory.Plus.quasiIso 𝒜) := sorry

/-- Stacks 05TN: every chosen right derived functor of `G` is isomorphic to the functor
computed by a lifted functorial injective resolution.  This is the uniqueness form of
`lift_comp_isRightDerivedFunctor`; it deliberately states only `IsIsomorphic`, so no public
choice of an `Iso` depends on the right-derived proof witness. -/
@[stacks 05TN]
theorem isIsomorphic_rightDerived_lift
    {D : Type w} [Category.{v₂} D] {E : Type u₂} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus 𝒜 ⥤ D)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso 𝒜)]
    (J : HomotopyCategory.Plus.InjectiveResolutionFunctor 𝒜)
    (L : D ⥤ HomotopyCategory.Plus.Injective 𝒜)
    (hL : Localization.Lifting Q (HomotopyCategory.Plus.quasiIso 𝒜) J.toFunctor L)
    (G : HomotopyCategory.Plus 𝒜 ⥤ E)
    (RG : D ⥤ E)
    (α : G ⟶ Q ⋙ RG)
    [RG.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso 𝒜)] :
    IsIsomorphic RG (L ⋙ HomotopyCategory.Plus.Injective.ι 𝒜 ⋙ G) := sorry

section Triangulated

variable {D : Type w} [Category.{v₂} D]
  [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Stacks 05TN: a lift of a functorial bounded-below injective resolution
through an exact functor whose map on arrows is essentially surjective is
exact. The result is Prop-valued because the induced shift comparison is
canonical only up to the lift comparison isomorphism. -/
@[stacks 05TN]
theorem lift_exact
    (Q : HomotopyCategory.Plus 𝒜 ⥤ D)
    [Q.CommShift ℤ] [Q.IsTriangulated] [Q.mapArrow.EssSurj]
    (J : HomotopyCategory.Plus.InjectiveResolutionFunctor 𝒜)
    (L : D ⥤ HomotopyCategory.Plus.Injective 𝒜)
    (hL : Localization.Lifting Q (HomotopyCategory.Plus.quasiIso 𝒜) J.toFunctor L) :
    L.HasTriangulatedStructure := sorry

/-- Stacks 05TN, Remark 13.25.2: after applying an additive functor to
bounded-below complexes, the factorization through an exact lift of a
functorial injective resolution remains exact. This is the reusable
homotopy-valued form of the factorization through `K⁺(𝒜)`. -/
@[stacks 05TN]
theorem lift_comp_mapHomotopyCategoryPlus_exact
    {ℬ : Type u₂} [Category.{v₃} ℬ] [Abelian ℬ]
    (Q : HomotopyCategory.Plus 𝒜 ⥤ D)
    [Q.CommShift ℤ] [Q.IsTriangulated] [Q.mapArrow.EssSurj]
    (J : HomotopyCategory.Plus.InjectiveResolutionFunctor 𝒜)
    (L : D ⥤ HomotopyCategory.Plus.Injective 𝒜)
    (hL : Localization.Lifting Q (HomotopyCategory.Plus.quasiIso 𝒜) J.toFunctor L)
    (F : 𝒜 ⥤ ℬ) [F.Additive] :
    Functor.HasTriangulatedStructure
      (L ⋙ HomotopyCategory.Plus.Injective.ι 𝒜 ⋙ F.mapHomotopyCategoryPlus) := sorry

end Triangulated

end CategoryTheory.HomotopyCategory.Plus.InjectiveResolutionFunctor
