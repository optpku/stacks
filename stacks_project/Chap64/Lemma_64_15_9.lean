module

import StacksCheckRecall
public import ReasLib.LinearAlgebra.Trace.Coinvariants

universe u v w x

open Ring
open scoped MonoidAlgebra Ring

/- Lemma 64.15.9 (1). The coinvariants of a finite projective monoid-algebra
module are finite projective over the coefficient ring. -/
@[stacks 03UD] #check (MonoidAlgebra.Coinvariants.finiteProjective :
    ∀ (Λ : Type u) (G : Type v) (P : Type x) [Ring Λ] [Monoid G] [AddCommGroup P]
    [Module (Λ[G]) P] [Module Λ P] [Finite G] [IsScalarTower Λ (Λ[G]) P]
    [Module.Finite (Λ[G]) P] [Module.Projective (Λ[G]) P],
    Module.FiniteProjective Λ (MonoidAlgebra.Coinvariants Λ G P))

/- Lemma 64.15.9 (2). The degree-one action on coinvariants generates the
natural-number action, independently of the degree-one lift. -/
@[stacks 03UD] #check (MonoidAlgebra.Coinvariants.natAction :
    ∀ {Λ : Type u} {G : Type v} {Γ : Type w} [Ring Λ] [Group G] [Monoid Γ]
    (S : NatMonoidExtension G Γ) (P : Type x)
    [AddCommGroup P] [Module (Λ[Γ]) P] [Module (Λ[G]) P] [Module Λ P]
    [IsScalarTower Λ (Λ[G]) P] [IsScalarTower Λ (Λ[Γ]) P]
    [MonoidAlgebra.IsRestrictionAlongInl Λ S P],
    Multiplicative ℕ →* Module.End Λ (MonoidAlgebra.Coinvariants Λ G P))

/- Lemma 64.15.9 (3). For the nonnegative monoid of an integer group extension
with finite kernel, the trace of one on coinvariants equals the sum of centralizer
traces over kernel-group conjugacy classes of degree-one elements. -/
@[stacks 03UD] #check (LinearMap.FiniteProjective.trace_one_coinvariants :
    ∀ {Λ : Type u} {G : Type v} {E : Type w} [Ring Λ] [Group G] [Group E] [Finite G]
    (T : GroupExtension G E (Multiplicative ℤ)) (P : Type x)
    [AddCommGroup P] [Module (Λ[NatMonoidExtension.nonneg T]) P]
    [Module (Λ[G]) P] [Module Λ P]
    [IsScalarTower Λ (Λ[G]) P] [Module.Finite (Λ[G]) P] [Module.Projective (Λ[G]) P]
    [IsScalarTower Λ (Λ[NatMonoidExtension.nonneg T]) P]
    [MonoidAlgebra.IsRestrictionAlongInl Λ (NatMonoidExtension.ofGroupExtension T) P],
    (LinearMap.FiniteProjective.traceNatural
      (MonoidAlgebra.Coinvariants.oneEnd (NatMonoidExtension.ofGroupExtension T) P) : Λ♮) =
      ∑ᶠ c : (NatMonoidExtension.ofGroupExtension T).DegreeOneGConjClass,
        LinearMap.FiniteProjective.conjClassTrace (NatMonoidExtension.ofGroupExtension T) P c)
