module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.ObjectProperty.Cover

/-!
# Cohomological-Dimension Functions

This file packages the categorical input used by dimension-lowering resolutions in an abelian
category.  The numerical function is kept separate from complex-level convergence conditions:
its zero locus supplies monomorphic replacements, while biproducts and short exact sequences
carry the two dimension estimates.
-/

@[expose] public section

open CategoryTheory.Limits
open scoped ZeroObject

universe v u

namespace CategoryTheory.CohomologicalDimension

open ObjectProperty

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The object property consisting of the objects on which `d` vanishes. -/
@[stacks 07K6]
def zeroLocus (d : A → WithTop ℕ) : ObjectProperty A :=
  fun X ↦ d X = 0

namespace ZeroLocus

/-- Membership in the zero locus is the numerical condition `d X = 0`. -/
@[simp]
theorem mem_iff (d : A → WithTop ℕ) (X : A) :
    zeroLocus d X ↔ d X = 0 := sorry

end ZeroLocus

/-- 07K6 (Lemma 13.32.1): the categorical axioms on a cohomological-dimension function.

Every object embeds into the zero locus, binary biproducts satisfy the maximum estimate, and the
right term of a short exact sequence has dimension at most the maximum of the middle dimension
and the predecessor of the left dimension. -/
@[stacks 07K6]
class IsFunction (d : A → WithTop ℕ) : Prop where
  /-- Every object embeds monomorphically into an object of dimension zero. -/
  hasMonoEmbedding : HasMonoEmbedding (zeroLocus d)
  /-- The dimension of a binary biproduct is bounded by the maximum of the two dimensions. -/
  biprod_le_max (X Y : A) : d (X ⊞ Y) ≤ max (d X) (d Y)
  /-- The right-term estimate associated to a short exact sequence. -/
  shortExact_right_le_max {S : ShortComplex A} (hS : S.ShortExact) :
    d S.X₃ ≤ max (d S.X₁ - 1) (d S.X₂)

attribute [instance] IsFunction.hasMonoEmbedding

namespace IsFunction

/-- 07K6 (Lemma 13.32.1): the three source conditions, exposed together as the semantic
specification of a cohomological-dimension function. -/
@[stacks 07K6]
theorem axioms_iff (d : A → WithTop ℕ) :
    IsFunction d ↔
      (∀ X : A, ∃ Y : A, d Y = 0 ∧ ∃ f : X ⟶ Y, Mono f) ∧
        (∀ X Y : A, d (X ⊞ Y) ≤ max (d X) (d Y)) ∧
          (∀ {S : ShortComplex A}, S.ShortExact →
            d S.X₃ ≤ max (d S.X₁ - 1) (d S.X₂)) := sorry

/-- The constant-zero function is a cohomological-dimension function. -/
instance instZero : IsFunction (fun _ : A ↦ (0 : WithTop ℕ)) := sorry

variable {d : A → WithTop ℕ} [h_d : IsFunction d]

include h_d

/-- A zero object has dimension zero. -/
@[stacks 07K6]
theorem zero_eq : d (0 : A) = 0 := sorry

/-- A cohomological-dimension function takes equal values on isomorphic objects. -/
theorem eq_of_iso {X Y : A} (e : X ≅ Y) : d X = d Y := sorry

end IsFunction

namespace ZeroLocus

/-- The zero locus contains a zero object. -/
instance containsZero {d : A → WithTop ℕ} [IsFunction d] :
    (zeroLocus d).ContainsZero := sorry

/-- The zero locus is closed under isomorphisms. -/
instance closedUnderIso {d : A → WithTop ℕ} [IsFunction d] :
    (zeroLocus d).IsClosedUnderIsomorphisms := sorry

/-- The zero locus is closed under binary biproducts. -/
theorem biprod_eq_zero {d : A → WithTop ℕ} [IsFunction d]
    {X Y : A} (hX : d X = 0) (hY : d Y = 0) :
    d (X ⊞ Y) = 0 := sorry

/-- The zero locus is closed under binary products. -/
instance closedUnderProducts {d : A → WithTop ℕ} [IsFunction d] :
    (zeroLocus d).IsClosedUnderBinaryProducts := sorry

/-- The zero locus is closed under binary coproducts. -/
instance closedUnderCoproducts {d : A → WithTop ℕ} [IsFunction d] :
    (zeroLocus d).IsClosedUnderBinaryCoproducts := sorry

/-- In a short exact sequence, zero dimension of the left and middle terms implies zero
dimension of the right term. -/
theorem right_eq_zero_of_shortExact {d : A → WithTop ℕ} [IsFunction d]
    {S : ShortComplex A} (hS : S.ShortExact)
    (h₁ : d S.X₁ = 0) (h₂ : d S.X₂ = 0) : d S.X₃ = 0 := sorry

end ZeroLocus

namespace IsFunction

variable {d : A → WithTop ℕ} [h_d : IsFunction d]

include h_d

/-- The general one-step dimension estimate for the cokernel of a biproduct lift. -/
@[stacks 07K6]
theorem cokernelBiprodLift_le {X Y M : A} (ι : X ⟶ M) [Mono ι] (f : X ⟶ Y) :
    d (cokernel (biprod.lift ι f)) ≤ max (d X - 1) (max (d M) (d Y)) := sorry

/-- If the first biproduct summand has dimension zero, the one-step cokernel estimate depends
only on the dimensions of the source and the other summand. -/
theorem cokernelBiprodLift_le_max {X Y M : A} (ι : X ⟶ M) [Mono ι]
    (f : X ⟶ Y) (hM : d M = 0) :
    d (cokernel (biprod.lift ι f)) ≤ max (d X - 1) (d Y) := sorry

/-- If all three objects in an elementary replacement step have dimension zero, then its new
cokernel term also has dimension zero. -/
@[stacks 07K6]
theorem cokernelBiprodLift_eq_zero {X Y M : A} (ι : X ⟶ M) [Mono ι]
    (f : X ⟶ Y) (hX : d X = 0) (hY : d Y = 0) (hM : d M = 0) :
    d (cokernel (biprod.lift ι f)) = 0 := sorry

end IsFunction

end CategoryTheory.CohomologicalDimension
