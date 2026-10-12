/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.RelativeNoetherianApproximation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

/-!
# Relative finite-presentation approximation

This file records directed affine-limit presentations of quasi-compact, quasi-separated schemes
by schemes of finite presentation over a fixed quasi-separated base.
-/

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Limit

/-- Fixed data form a relative finite-presentation approximation when their cone is limiting,
their stage maps and transitions are compatible over the base, every transition is affine, and
every stage map is of finite presentation. -/
def IsRelativeFinitePresentationApproximation {I : Type u} [Preorder I]
    {X S : Scheme.{u}} (f : X ⟶ S) (D : OrderDual I ⥤ Scheme.{u})
    (π : (Functor.const (OrderDual I)).obj X ⟶ D)
    (σ : ∀ j : I, D.obj j ⟶ S) : Prop :=
  Nonempty (IsLimit (⟨X, π⟩ : Cone D)) ∧
    (∀ {j k : I} (hjk : j ≤ k), D.map (homOfLE hjk) ≫ σ j = σ k) ∧
    (∀ j : I, π.app j ≫ σ j = f) ∧
    (∀ {j k : I} (hjk : j ≤ k), IsAffineHom (D.map (homOfLE hjk))) ∧
    ∀ j : I, Scheme.Hom.FinitePresentation (σ j)

/-- The relative finite-presentation approximation predicate is equivalent to its limiting,
compatibility, factorization, affine-transition, and finite-presentation conditions. -/
theorem isRelativeFinitePresentationApproximation_iff {I : Type u} [Preorder I]
    {X S : Scheme.{u}} (f : X ⟶ S) (D : OrderDual I ⥤ Scheme.{u})
    (π : (Functor.const (OrderDual I)).obj X ⟶ D)
    (σ : ∀ j : I, D.obj j ⟶ S) :
    IsRelativeFinitePresentationApproximation f D π σ ↔
      Nonempty (IsLimit (⟨X, π⟩ : Cone D)) ∧
        (∀ {j k : I} (hjk : j ≤ k), D.map (homOfLE hjk) ≫ σ j = σ k) ∧
        (∀ j : I, π.app j ≫ σ j = f) ∧
        (∀ {j k : I} (hjk : j ≤ k), IsAffineHom (D.map (homOfLE hjk))) ∧
        ∀ j : I, Scheme.Hom.FinitePresentation (σ j) :=
  Iff.rfl

/-- Every morphism from a quasi-compact, quasi-separated scheme to a quasi-separated scheme
admits a directed relative finite-presentation approximation with affine transition morphisms. -/
theorem exists_relativeFinitePresentationApproximation
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace X] [QuasiSeparatedSpace X]
    [QuasiSeparatedSpace S] :
    ∃ (I : Type u), ∃ (_ : Preorder I), ∃ (_ : Nonempty I),
      ∃ (_ : IsDirected I (· ≤ ·)), ∃ (D : OrderDual I ⥤ Scheme.{u}),
        ∃ (π : (Functor.const (OrderDual I)).obj X ⟶ D),
          ∃ (σ : ∀ j : I, D.obj j ⟶ S),
            IsRelativeFinitePresentationApproximation f D π σ := sorry

end AlgebraicGeometry.Scheme.Limit
