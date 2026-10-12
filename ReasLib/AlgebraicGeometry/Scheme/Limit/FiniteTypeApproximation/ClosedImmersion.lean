/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.ClosedSubscheme
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Factorization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Operations

/-!
# Finite-presentation approximation by closed immersions

This file records directed limit presentations of locally finite type scheme morphisms by
quasi-compact, quasi-separated schemes of finite presentation, with closed-immersion transition
maps and projections.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Limit

/-- Fixed data form a closed-immersion finite-presentation approximation when their cone is
limiting, their structure maps are compatible over the base, every stage is quasi-compact and
quasi-separated and of finite presentation over the base, and all transition maps and limit
projections are closed immersions. -/
def IsClosedImmersionFinitePresentationApproximation {I : Type u} [Preorder I]
    {X S : Scheme.{u}} (f : X ⟶ S) (D : OrderDual I ⥤ Scheme.{u})
    (π : (Functor.const (OrderDual I)).obj X ⟶ D)
    (σ : ∀ j : I, D.obj j ⟶ S) : Prop :=
  Nonempty (IsLimit (⟨X, π⟩ : Cone D)) ∧
    (∀ {j k : I} (hjk : j ≤ k), D.map (homOfLE hjk) ≫ σ j = σ k) ∧
    (∀ j : I, π.app j ≫ σ j = f) ∧
    (∀ j : I, Scheme.Hom.FinitePresentation (σ j)) ∧
    (∀ j : I, CompactSpace (D.obj j)) ∧
    (∀ j : I, QuasiSeparatedSpace (D.obj j)) ∧
    (∀ {j k : I} (hjk : j ≤ k), IsClosedImmersion (D.map (homOfLE hjk))) ∧
    ∀ j : I, IsClosedImmersion (π.app j)

/-- A closed-immersion finite-presentation approximation is equivalently a limiting compatible
system over the base whose stages are quasi-compact and quasi-separated and of finite
presentation, and whose transition maps and limit projections are closed immersions. -/
theorem isClosedImmersionFinitePresentationApproximation_iff {I : Type u} [Preorder I]
    {X S : Scheme.{u}} (f : X ⟶ S) (D : OrderDual I ⥤ Scheme.{u})
    (π : (Functor.const (OrderDual I)).obj X ⟶ D)
    (σ : ∀ j : I, D.obj j ⟶ S) :
    IsClosedImmersionFinitePresentationApproximation f D π σ ↔
      Nonempty (IsLimit (⟨X, π⟩ : Cone D)) ∧
        (∀ {j k : I} (hjk : j ≤ k), D.map (homOfLE hjk) ≫ σ j = σ k) ∧
        (∀ j : I, π.app j ≫ σ j = f) ∧
        (∀ j : I, Scheme.Hom.FinitePresentation (σ j)) ∧
        (∀ j : I, CompactSpace (D.obj j)) ∧
        (∀ j : I, QuasiSeparatedSpace (D.obj j)) ∧
        (∀ {j k : I} (hjk : j ≤ k), IsClosedImmersion (D.map (homOfLE hjk))) ∧
        ∀ j : I, IsClosedImmersion (π.app j) := sorry

namespace IsClosedImmersionFinitePresentationApproximation

/-- A locally finite type morphism from a quasi-compact, quasi-separated scheme to a
quasi-separated scheme admits a directed closed-immersion finite-presentation approximation. -/
theorem exists_of_locallyOfFiniteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [CompactSpace X] [QuasiSeparatedSpace X] [QuasiSeparatedSpace S] :
    ∃ (I : Type u), ∃ (_ : Preorder I), ∃ (_ : Nonempty I),
      ∃ (_ : IsDirected I (· ≤ ·)), ∃ (D : OrderDual I ⥤ Scheme.{u}),
        ∃ (π : (Functor.const (OrderDual I)).obj X ⟶ D),
          ∃ (σ : ∀ j : I, D.obj j ⟶ S),
            IsClosedImmersionFinitePresentationApproximation f D π σ := sorry

end IsClosedImmersionFinitePresentationApproximation

end AlgebraicGeometry.Scheme.Limit
