/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import ReasLib.RingTheory.GradedAlgebra.GeneratedBy
public import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u

namespace GradedAlgebra

variable {A : Type u} [CommRing A]

/-- A finite set of positive-degree homogeneous generators of a graded algebra. -/
@[stacks 0BXE]
structure PositiveGenerators (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜] where
  /-- The finite set of generators. -/
  elems : Finset A
  /-- The degree assigned to each generator. -/
  degree : {x // x ∈ elems} → ℕ
  /-- The generators together with the degree-zero part generate the algebra. -/
  generates : Algebra.adjoin (𝒜 0) (elems : Set A) = ⊤
  /-- Each generator is homogeneous of its assigned degree. -/
  homogeneous : ∀ x : {x // x ∈ elems}, x.1 ∈ 𝒜 (degree x)
  /-- Every assigned generator degree is positive. -/
  positive : ∀ x : {x // x ∈ elems}, 0 < degree x

namespace PositiveGenerators

variable {𝒜 : ℕ → Submodule ℤ A} [GradedAlgebra 𝒜]

/-- Constructs positive generators from a finite set and its assigned degrees. -/
def ofFinset (elems : Finset A) (degree : {x // x ∈ elems} → ℕ)
    (generates : Algebra.adjoin (𝒜 0) (elems : Set A) = ⊤)
    (homogeneous : ∀ x : {x // x ∈ elems}, x.1 ∈ 𝒜 (degree x))
    (positive : ∀ x : {x // x ∈ elems}, 0 < degree x) : PositiveGenerators 𝒜 where
  elems := elems
  degree := degree
  generates := generates
  homogeneous := homogeneous
  positive := positive

/-- The common period given by the least common multiple of the generator degrees. -/
@[stacks 0BXE]
def period (G : PositiveGenerators 𝒜) : ℕ := G.elems.attach.lcm G.degree

/-- Each generator degree divides the period. -/
theorem degree_dvd_period (G : PositiveGenerators 𝒜) (x : {x // x ∈ G.elems}) :
    G.degree x ∣ G.period := sorry

/-- The period is positive. -/
theorem period_pos (G : PositiveGenerators 𝒜) : 0 < G.period := sorry

/-- The defining properties of positive homogeneous generators and their period. -/
@[stacks 0BXE]
theorem spec (G : PositiveGenerators 𝒜) :
    Algebra.adjoin (𝒜 0) (G.elems : Set A) = ⊤ ∧
      (∀ x : {x // x ∈ G.elems}, x.1 ∈ 𝒜 (G.degree x)) ∧
        (∀ x : {x // x ∈ G.elems}, 0 < G.degree x) ∧
          (∀ x : {x // x ∈ G.elems}, G.degree x ∣ G.period) ∧ 0 < G.period := sorry

end PositiveGenerators

end GradedAlgebra
