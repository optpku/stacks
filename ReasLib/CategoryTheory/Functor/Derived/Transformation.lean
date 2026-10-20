module

public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Subset.Left
public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Left
public import ReasLib.CategoryTheory.NatTrans.IsIso
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived Natural Transformations

This leaf gives generic isomorphism criteria for natural transformations
between total left-derived functors.  It is independent of tensor products,
complexes, and any chosen localization model.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.LeftDerived

variable {K : Type u₁} {H : Type u₂}
variable [Category.{v₁} K] [Category.{v₂} H]

/-- A natural transformation which is an isomorphism at an object computing both left-derived
functors induces an isomorphism at the corresponding localized object. -/
theorem natTrans_app_isIso_of_computesAt
    (S : MorphismProperty K) (F G : K ⥤ H) (τ : F ⟶ G) {P : K}
    [S.ContainsIdentities]
    [F.HasLeftDerivedFunctor S] [G.HasLeftDerivedFunctor S]
    [F.HasPointwiseLeftDerivedFunctor S] [G.HasPointwiseLeftDerivedFunctor S]
    [LeftDerived.ComputesAt F S P] [LeftDerived.ComputesAt G S P]
    [IsIso (τ.app P)] :
    IsIso ((LeftDerived.mapNatTrans S.Q S τ).app (S.Q.obj P)) := sorry

/-- A natural transformation is an isomorphism after total left derivation when every object has
a denominator from a point at which both functors compute their derived values and the original
transformation is invertible there. -/
theorem natTrans_isIso_of_computesAt
    (S : MorphismProperty K) (F G : K ⥤ H) (τ : F ⟶ G)
    [S.ContainsIdentities]
    [F.HasLeftDerivedFunctor S] [G.HasLeftDerivedFunctor S]
    [F.HasPointwiseLeftDerivedFunctor S] [G.HasPointwiseLeftDerivedFunctor S]
    (P : ObjectProperty K)
    (hP_reaches :
      ∀ X : K, ∃ (X' : K) (s : X' ⟶ X), P X' ∧ S s)
    (hP_F : ∀ X : K, P X → LeftDerived.ComputesAt F S X)
    (hP_G : ∀ X : K, P X → LeftDerived.ComputesAt G S X)
    (hP_τ : ∀ X : K, P X → IsIso (τ.app X)) :
    IsIso (LeftDerived.mapNatTrans S.Q S τ) := sorry

/-- Lemma 22.33.3 (09S3): a natural transformation becomes an isomorphism after total left
derivation when both functors invert denominators between a denominator-cofinal good subset and
the original transformation is invertible on that subset. -/
@[stacks 09S3]
theorem natTrans_isIso_of_subset
    (S : MorphismProperty K) (F G : K ⥤ H) (τ : F ⟶ G)
    [S.IsSaturatedMultiplicativeSystem]
    [F.HasLeftDerivedFunctor S] [G.HasLeftDerivedFunctor S]
    (P : ObjectProperty K)
    (hP_reaches :
      ∀ X : K, ∃ (X' : K) (s : X' ⟶ X), P X' ∧ S s)
    (hP_F : ∀ {X X' : K} (s : X ⟶ X'), P X → P X' → S s → IsIso (F.map s))
    (hP_G : ∀ {X X' : K} (s : X ⟶ X'), P X → P X' → S s → IsIso (G.map s))
    (hP_τ : ∀ X : K, P X → IsIso (τ.app X)) :
    IsIso (LeftDerived.mapNatTrans S.Q S τ) := sorry

end CategoryTheory.Functor.LeftDerived
