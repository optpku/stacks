/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sequential.Grothendieck
public import ReasLib.Algebra.Category.ModuleCat.Sequential.HomologicalComplex
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Characterization
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Unbounded.Acyclic.Right
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Grothendieck
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived inverse limits of sequential varying-ring modules

For an inverse system `A₀ ← A₁ ← A₂ ← ⋯`, this file constructs the inverse-limit functor from
modules over the varying ring system to modules over `lim Aₙ`.  The construction first forms the
stagewise restriction-of-scalars diagram as a functor-valued inverse system, then uses
`Functor.flip` and the ordinary limit functor.  Its total right derived functor and the five
source clauses are exposed independently.

@stack 091D
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite

noncomputable section

universe u

namespace CategoryTheory.SequentialInverseSystem.ModuleSystem.DerivedLimit

-- Local instance justification (defeq pin): all source-facing derived-category expressions use
-- Mathlib's standard model; this does not install a global choice of derived category.
attribute [local instance] HasDerivedCategory.standard

variable (A : ℕ → Type u) [∀ n, CommRing (A n)]
variable (ρ : ∀ n, A (n + 1) →+* A n)

/-- The inverse-limit ring of the sequential ring system `(A, ρ)`. -/
@[stacks 091D "inverse-limit ring of a sequential ring system"]
abbrev limitRing : Type u :=
  ((limit (sequentialRingSystem A ρ) : CommRingCat.{u}) : Type u)

/-- Modules over the inverse-limit ring of `(A, ρ)`. -/
@[stacks 091D "module category over the inverse-limit ring"]
abbrev limitModule := ModuleCat.{u} (limitRing A ρ)

/-- The target derived category for the varying-ring derived inverse limit. -/
@[stacks 091D "target category of the varying-ring derived limit"]
abbrev target := DerivedCategory (limitModule A ρ)

/-- The canonical projection `lim Aₙ → Aₙ`. -/
@[stacks 091D "projection from the inverse-limit ring"]
abbrev limitProjection (n : ℕ) : limitRing A ρ →+* A n :=
  (limit.π (sequentialRingSystem A ρ) (op n)).hom

/-- Each stage ring is canonically an algebra over the inverse-limit ring. -/
@[stacks 091D "stage algebra over the inverse-limit ring", instance]
instance stageAlgebra (n : ℕ) : Algebra (limitRing A ρ) (A n) :=
  RingHom.toAlgebra (limitProjection A ρ n)

/-- Successive limit projections are compatible with the ring-system transition. -/
@[stacks 091D "compatibility of inverse-limit ring projections"]
theorem limitProjection_comp (n : ℕ) :
    limitProjection A ρ n =
      ((sequentialRingSystem A ρ).stepMap n).hom.comp (limitProjection A ρ (n + 1)) := sorry

/-- Evaluation at stage `n`, followed by restriction of scalars along `lim Aₙ → Aₙ`. -/
@[stacks 091D "fixed-base evaluation of a varying-ring module"]
abbrev limitEvaluation (n : ℕ) :
    SeqRingMod.{u, u} A ρ ⥤ limitModule A ρ :=
  sequentialRingedModuleEvaluation A ρ n ⋙
    ModuleCat.restrictScalars (limitProjection A ρ n)

/-- The transition between successive fixed-base stage evaluations. -/
@[stacks 091D "transition between fixed-base stage evaluations"]
abbrev limitEvaluationStep (n : ℕ) :
    limitEvaluation A ρ (n + 1) ⟶ limitEvaluation A ρ n :=
  (Functor.whiskerRight
      (sequentialRingedModuleEvaluationStep A ρ n)
      (ModuleCat.restrictScalars (limitProjection A ρ (n + 1)))) ≫
    Functor.whiskerLeft (sequentialRingedModuleEvaluation A ρ n)
      ((ModuleCat.restrictScalarsComp'
        (limitProjection A ρ (n + 1))
        ((sequentialRingSystem A ρ).stepMap n).hom (limitProjection A ρ n)
        (limitProjection_comp A ρ n)).inv)

/-- The functor-valued inverse system of fixed-base stage evaluations. -/
@[stacks 091D "inverse system of fixed-base evaluation functors"]
abbrev limitEvaluationSystem :
    ℕᵒᵖ ⥤ (SeqRingMod.{u, u} A ρ ⥤ limitModule A ρ) :=
  @Functor.ofOpSequence (SeqRingMod.{u, u} A ρ ⥤ limitModule A ρ) _
    (fun n ↦ limitEvaluation A ρ n) (fun n ↦ limitEvaluationStep A ρ n)

/-- The functor assigning to a varying-ring module its fixed-base sequential inverse system. -/
@[stacks 091D "fixed-base tower functor for varying-ring modules"]
abbrev limitTowerFunctor :
    SeqRingMod.{u, u} A ρ ⥤ SequentialInverseSystem (limitModule A ρ) :=
  (limitEvaluationSystem A ρ).flip

/-- The fixed-base inverse system attached to a varying-ring module. -/
@[stacks 091D "fixed-base tower of a varying-ring module"]
abbrev ringedModuleLimitTower (M : SeqRingMod.{u, u} A ρ) :
    SequentialInverseSystem (limitModule A ρ) :=
  (limitTowerFunctor A ρ).obj M

/-- The inverse-limit functor from varying-ring modules to modules over `lim Aₙ`. -/
@[stacks 091D "inverse limit of sequential varying-ring modules"]
abbrev ringedModuleInverseLimitFunctor :
    SeqRingMod.{u, u} A ρ ⥤ limitModule A ρ :=
  limitTowerFunctor A ρ ⋙ lim

/-- The fixed-base tower functor is additive. -/
@[stacks 091D "additivity of the fixed-base tower functor", instance]
instance limitTowerFunctor_additive : (limitTowerFunctor A ρ).Additive := sorry

/-- The inverse-limit functor on varying-ring modules is additive. -/
@[stacks 091D "additivity of the varying-ring inverse-limit functor", instance]
instance ringedModuleInverseLimitFunctor_additive :
    (ringedModuleInverseLimitFunctor A ρ).Additive := sorry

/-- A varying-ring module placed in cohomological degree `0`. -/
@[stacks 091D "degree-zero varying-ring module complex"]
abbrev degreeZero (M : SeqRingMod.{u, u} A ρ) :
    DerivedCategory (SeqRingMod.{u, u} A ρ) :=
  (DerivedCategory.singleFunctor (SeqRingMod.{u, u} A ρ) (0 : ℤ)).obj M

/-- Lemma 15.88.1: the inverse-limit functor on sequential varying-ring modules has a total
right derived functor with values in `D(lim Aₙ)`. -/
@[stacks 091D, stacks 091E "derived inverse limit for sequential varying-ring modules"]
abbrev ringedModuleDerivedInverseLimitFunctor :
    DerivedCategory (SeqRingMod.{u, u} A ρ) ⥤ target A ρ :=
  @Functor.RightDerived.KInjective.functor.{u + 1, u + 1, u + 1, u + 1, u + 1, u, u}
    _ _ _ _ _ _ _ _ (ringedModuleInverseLimitFunctor A ρ) _ _
    (Functor.RightDerived.KInjective.hasDerived.{u + 1, u + 1, u + 1, u + 1, u, u}
      (ringedModuleInverseLimitFunctor A ρ))

/-- Lemma 15.88.1 (1): the higher derived inverse limits of a varying-ring module vanish in
degrees strictly greater than `1`. -/
@[stacks 091D "(1), higher derived inverse-limit vanishing"]
theorem homology_isZero_of_one_lt
    (M : SeqRingMod.{u, u} A ρ) (p : ℕ) (hp : 1 < p) :
    IsZero ((DerivedCategory.homologyFunctor (limitModule A ρ) (p : ℤ)).obj
      ((ringedModuleDerivedInverseLimitFunctor A ρ).obj (degreeZero A ρ M))) := sorry

/-- Lemma 15.88.1 (2): the derived inverse limit of a module system is the Milnor derived limit
of its fixed-base tower, equivalently the object represented by the product-difference complex in
degrees `0` and `1`. -/
@[stacks 091D "(2), product-difference model for derived inverse limit"]
theorem isDerivedLimit_of_object (M : SeqRingMod.{u, u} A ρ) :
    Nonempty (CategoryTheory.IsDerivedLimit
      ((ringedModuleLimitTower A ρ M) ⋙
        DerivedCategory.singleFunctor (limitModule A ρ) (0 : ℤ))
      ((ringedModuleDerivedInverseLimitFunctor A ρ).obj (degreeZero A ρ M))) := sorry

/-- Lemma 15.88.1 (3): a Mittag-Leffler varying-ring module system is right acyclic for inverse
limit. -/
@[stacks 091D "(3), Mittag-Leffler systems are inverse-limit acyclic"]
theorem rightAcyclic_of_isMittagLeffler
    (M : SeqRingMod.{u, u} A ρ)
    (hM : SequentialInverseSystem.IsMittagLeffler (ringedModuleLimitTower A ρ M)) :
    Functor.RightAcyclic (ringedModuleInverseLimitFunctor A ρ) M := sorry

/-- Lemma 15.88.1 (4): every derived varying-ring module has a cochain representative whose
terms are right acyclic for inverse limit. -/
@[stacks 091D "(4), termwise inverse-limit-acyclic representative"]
theorem exists_termwiseRightAcyclic_representative
    (K : DerivedCategory (SeqRingMod.{u, u} A ρ)) :
    ∃ (L : CochainComplex (SeqRingMod.{u, u} A ρ) ℤ)
      (e : DerivedCategory.Q.obj L ≅ K),
      ∀ i : ℤ, Functor.RightAcyclic
        (ringedModuleInverseLimitFunctor A ρ) (L.X i) := sorry

/-- Lemma 15.88.1 (5): a termwise inverse-limit-acyclic cochain complex computes the total
derived inverse limit by applying ordinary inverse limit degreewise. -/
@[stacks 091D "(5), computation by a termwise acyclic complex"]
theorem computes_of_termwiseRightAcyclic
    (K : CochainComplex (SeqRingMod.{u, u} A ρ) ℤ)
    (hK : ∀ i : ℤ, Functor.RightAcyclic
      (ringedModuleInverseLimitFunctor A ρ) (K.X i)) :
    Functor.RightDerived.ComputesAt
      (Functor.Homotopy.toDerived (ringedModuleInverseLimitFunctor A ρ))
      (HomotopyCategory.quasiIso
        (SeqRingMod.{u, u} A ρ) (ComplexShape.up ℤ))
      ((HomotopyCategory.quotient
        (SeqRingMod.{u, u} A ρ) (ComplexShape.up ℤ)).obj K) := sorry

end CategoryTheory.SequentialInverseSystem.ModuleSystem.DerivedLimit
