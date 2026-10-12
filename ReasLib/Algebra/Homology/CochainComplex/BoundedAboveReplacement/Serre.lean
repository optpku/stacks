/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement
public import ReasLib.CategoryTheory.ObjectProperty.Cover
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded-Above Replacements in a Serre Subcategory

This file records the seeded subcomplex replacement used to compare a Serre
subcategory with the ambient bounded-above derived category.  The epi-lift
condition is supplied through `ObjectProperty.HasEpiLift`.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open HomologicalComplex

universe v u

namespace CochainComplex.Minus.TermsIn

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.IsSerreClass] [P.HasEpiLift]

/-- A bounded-above complex whose homology lies in `P` admits a termwise-`P`
subcomplex with acyclic cokernel, compatibly with prescribed degreewise
subobjects in `P`. -/
@[stacks 0FCL]
theorem exists_seeded_mono_of_homology
    (a : ℤ) (K : CochainComplex A ℤ) (hK : K.IsStrictlyLE a)
    (hH : ∀ n : ℤ, P (K.homology n))
    (B : ∀ n : ℤ, Subobject (K.X n))
    (hBmem : ∀ n : ℤ, P ((B n : Subobject (K.X n)) : A))
    (hBd :
      ∀ n : ℤ,
        ∃ β : ((B n : Subobject (K.X n)) : A) ⟶
            ((B (n + 1) : Subobject (K.X (n + 1))) : A),
          (B n).arrow ≫ K.d n (n + 1) = β ≫ (B (n + 1)).arrow) :
    ∃ (Q : CochainComplex A ℤ) (α : Q ⟶ K),
      Q.IsStrictlyLE a ∧ Mono α ∧ (cokernel α).Acyclic ∧
        (∀ n : ℤ, P (Q.X n)) ∧
        (∀ n : ℤ,
          ∃ i : ((B n : Subobject (K.X n)) : A) ⟶ Q.X n,
            i ≫ α.f n = (B n).arrow) := sorry

end CochainComplex.Minus.TermsIn
