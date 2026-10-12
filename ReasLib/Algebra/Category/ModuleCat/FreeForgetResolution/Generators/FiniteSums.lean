/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FreeForgetResolution.Generators

/-!
@stack 0G5U

# Finite-sum formulas for free-forgetful resolution generators

This leaf records the coefficientwise face and degeneracy formulas for finite families, `Finset`
supports, and `Finsupp` supports. The generator-level owners live in `Generators`.
-/

@[expose] public section

open CategoryTheory

universe u uι uκ

namespace CategoryTheory.ModuleCat.FreeForgetResolution

variable (R : Type u) [Ring R]

/-- The counit evaluates a finite weighted sum of free generators coefficientwise. -/
@[stacks 0G5U "free-module counit on finite sums"]
theorem counit.sum.freeMk {R : Type u} [Ring R]
    (M : ModuleCat R) {κ : Type uκ} [Fintype κ]
    (s : κ → R) (m : κ → M) :
    ((counit R).app M) (∑ j, s j • ModuleCat.freeMk (m j)) =
      ∑ j, s j • m j := sorry

/-- The comultiplication brackets a finite weighted sum of free generators coefficientwise. -/
@[stacks 0G5U "free-module comultiplication on finite sums"]
theorem comultiplication.sum.freeMk {R : Type u} [Ring R]
    (M : ModuleCat R) {κ : Type uκ} [Fintype κ]
    (s : κ → R) (m : κ → M) :
    ((comultiplication R).app M) (∑ j, s j • ModuleCat.freeMk (m j)) =
      ∑ j, s j • ModuleCat.freeMk (ModuleCat.freeMk (m j)) := sorry

/-- The zeroth face flattens a nested finite sum of free generators. -/
@[stacks 0G5U "zeroth face on nested free-module sums"]
theorem face.zero.nestedSum {R : Type u} [Ring R] (M : ModuleCat R)
    {ι : Type uι} {κ : ι → Type uκ} [Fintype ι] [∀ i, Fintype (κ i)]
    (r : ι → R) (s : ∀ i, κ i → R) (m : ∀ i, κ i → M) :
    (face R 0 (1 : Fin 2)).app M
        (∑ i, r i • ModuleCat.freeMk (∑ j, s i j • ModuleCat.freeMk (m i j))) =
      ∑ i, ∑ j, (r i * s i j) • ModuleCat.freeMk (m i j) := sorry

/-- The first face evaluates the inner finite sum inside every outer free generator. -/
@[stacks 0G5U "first face on nested free-module sums"]
theorem face.one.nestedSum {R : Type u} [Ring R] (M : ModuleCat R)
    {ι : Type uι} {κ : ι → Type uκ} [Fintype ι] [∀ i, Fintype (κ i)]
    (r : ι → R) (s : ∀ i, κ i → R) (m : ∀ i, κ i → M) :
    (face R 0 (0 : Fin 2)).app M
        (∑ i, r i • ModuleCat.freeMk (∑ j, s i j • ModuleCat.freeMk (m i j))) =
      ∑ i, r i • ModuleCat.freeMk (∑ j, s i j • m i j) := sorry

/-- The zeroth degeneracy adds one outer bracket to a nested finite sum. -/
@[stacks 0G5U "zeroth degeneracy on nested free-module sums"]
theorem degeneracy.zero.nestedSum {R : Type u} [Ring R] (M : ModuleCat R)
    {ι : Type uι} {κ : ι → Type uκ} [Fintype ι] [∀ i, Fintype (κ i)]
    (r : ι → R) (s : ∀ i, κ i → R) (m : ∀ i, κ i → M) :
    (degeneracy R 1 (1 : Fin 2)).app M
        (∑ i, r i • ModuleCat.freeMk (∑ j, s i j • ModuleCat.freeMk (m i j))) =
      ∑ i, r i • ModuleCat.freeMk
        (ModuleCat.freeMk (∑ j, s i j • ModuleCat.freeMk (m i j))) := sorry

/-- The first degeneracy brackets each inner generator in a nested finite sum. -/
@[stacks 0G5U "first degeneracy on nested free-module sums"]
theorem degeneracy.one.nestedSum {R : Type u} [Ring R] (M : ModuleCat R)
    {ι : Type uι} {κ : ι → Type uκ} [Fintype ι] [∀ i, Fintype (κ i)]
    (r : ι → R) (s : ∀ i, κ i → R) (m : ∀ i, κ i → M) :
    (degeneracy R 1 (0 : Fin 2)).app M
        (∑ i, r i • ModuleCat.freeMk (∑ j, s i j • ModuleCat.freeMk (m i j))) =
      ∑ i, r i • ModuleCat.freeMk
        (∑ j, s i j • ModuleCat.freeMk (ModuleCat.freeMk (m i j))) := sorry

/-!
The statements below are the finite-support core of the coefficientwise formulas. The
ambient-`Fintype` versions above remain the source-facing entry points; downstream arguments
should use these `Finset`/`Finsupp` forms whenever only a local finite support is available.
-/

/-- The counit evaluates a weighted sum over an arbitrary finite index set. -/
@[stacks 0G5U "free-module counit on Finset-supported sums"]
theorem counit.finset.freeMk {R : Type u} [Ring R]
    (M : ModuleCat R) {κ : Type uκ} (t : Finset κ)
    (s : κ → R) (m : κ → M) :
    ((counit R).app M) (∑ j ∈ t, s j • ModuleCat.freeMk (m j)) =
      ∑ j ∈ t, s j • m j := sorry

/-- The comultiplication brackets a weighted sum over an arbitrary finite index set. -/
@[stacks 0G5U "free-module comultiplication on Finset-supported sums"]
theorem comultiplication.finset.freeMk {R : Type u} [Ring R]
    (M : ModuleCat R) {κ : Type uκ} (t : Finset κ)
    (s : κ → R) (m : κ → M) :
    ((comultiplication R).app M) (∑ j ∈ t, s j • ModuleCat.freeMk (m j)) =
      ∑ j ∈ t, s j • ModuleCat.freeMk (ModuleCat.freeMk (m j)) := sorry

/-- The counit evaluates a finitely supported weighted sum of free generators. -/
@[stacks 0G5U "free-module counit on Finsupp-supported sums"]
theorem counit.finsupp.freeMk {R : Type u} [Ring R]
    (M : ModuleCat R) {κ : Type uκ} (v : κ →₀ R)
    (m : κ → M) :
    ((counit R).app M) (v.sum fun j a => a • ModuleCat.freeMk (m j)) =
      v.sum fun j a => a • m j := sorry

/-- The comultiplication brackets a finitely supported weighted sum of free generators. -/
@[stacks 0G5U "free-module comultiplication on Finsupp-supported sums"]
theorem comultiplication.finsupp.freeMk {R : Type u} [Ring R]
    (M : ModuleCat R) {κ : Type uκ} (v : κ →₀ R)
    (m : κ → M) :
    ((comultiplication R).app M) (v.sum fun j a => a • ModuleCat.freeMk (m j)) =
      v.sum fun j a => a • ModuleCat.freeMk (ModuleCat.freeMk (m j)) := sorry

/-- The zeroth face flattens a nested sum over arbitrary finite index sets. -/
@[stacks 0G5U "zeroth face on nested Finset-supported sums"]
theorem face.zero.nestedFinset {R : Type u} [Ring R] (M : ModuleCat R)
    {ι : Type uι} {κ : ι → Type uκ} (t : Finset ι) (u : ∀ i, Finset (κ i))
    (r : ι → R) (s : ∀ i, κ i → R) (m : ∀ i, κ i → M) :
    (face R 0 (1 : Fin 2)).app M
        (∑ i ∈ t, r i • ModuleCat.freeMk (∑ j ∈ u i, s i j • ModuleCat.freeMk (m i j))) =
      ∑ i ∈ t, ∑ j ∈ u i, (r i * s i j) • ModuleCat.freeMk (m i j) := sorry

/-- The first face evaluates each inner sum in a nested finite-support expression. -/
@[stacks 0G5U "first face on nested Finset-supported sums"]
theorem face.one.nestedFinset {R : Type u} [Ring R] (M : ModuleCat R)
    {ι : Type uι} {κ : ι → Type uκ} (t : Finset ι) (u : ∀ i, Finset (κ i))
    (r : ι → R) (s : ∀ i, κ i → R) (m : ∀ i, κ i → M) :
    (face R 0 (0 : Fin 2)).app M
        (∑ i ∈ t, r i • ModuleCat.freeMk (∑ j ∈ u i, s i j • ModuleCat.freeMk (m i j))) =
      ∑ i ∈ t, r i • ModuleCat.freeMk (∑ j ∈ u i, s i j • m i j) := sorry

/-- The zeroth degeneracy adds an outer bracket to a nested finite-support expression. -/
@[stacks 0G5U "zeroth degeneracy on nested Finset-supported sums"]
theorem degeneracy.zero.nestedFinset {R : Type u} [Ring R] (M : ModuleCat R)
    {ι : Type uι} {κ : ι → Type uκ} (t : Finset ι) (u : ∀ i, Finset (κ i))
    (r : ι → R) (s : ∀ i, κ i → R) (m : ∀ i, κ i → M) :
    (degeneracy R 1 (1 : Fin 2)).app M
        (∑ i ∈ t, r i • ModuleCat.freeMk (∑ j ∈ u i, s i j • ModuleCat.freeMk (m i j))) =
      ∑ i ∈ t, r i • ModuleCat.freeMk
        (ModuleCat.freeMk (∑ j ∈ u i, s i j • ModuleCat.freeMk (m i j))) := sorry

/-- The first degeneracy brackets every inner generator in a nested finite-support expression. -/
@[stacks 0G5U "first degeneracy on nested Finset-supported sums"]
theorem degeneracy.one.nestedFinset {R : Type u} [Ring R] (M : ModuleCat R)
    {ι : Type uι} {κ : ι → Type uκ} (t : Finset ι) (u : ∀ i, Finset (κ i))
    (r : ι → R) (s : ∀ i, κ i → R) (m : ∀ i, κ i → M) :
    (degeneracy R 1 (0 : Fin 2)).app M
        (∑ i ∈ t, r i • ModuleCat.freeMk (∑ j ∈ u i, s i j • ModuleCat.freeMk (m i j))) =
      ∑ i ∈ t, r i • ModuleCat.freeMk
        (∑ j ∈ u i, s i j • ModuleCat.freeMk (ModuleCat.freeMk (m i j))) := sorry

/-- The zeroth face flattens a nested finitely supported coefficient expression. -/
@[stacks 0G5U "zeroth face on nested Finsupp-supported sums"]
theorem face.zero.nestedFinsupp {R : Type u} [Ring R] (M : ModuleCat R)
    {ι : Type uι} {κ : ι → Type uκ} (r : ι →₀ R) (s : ∀ i, κ i →₀ R)
    (m : ∀ i, κ i → M) :
    (face R 0 (1 : Fin 2)).app M
        (r.sum fun i a => a • ModuleCat.freeMk
          ((s i).sum fun j b => b • ModuleCat.freeMk (m i j))) =
      r.sum fun i a => (s i).sum fun j b =>
        (a * b) • ModuleCat.freeMk (m i j) := sorry

/-- The first face evaluates each inner finitely supported coefficient expression. -/
@[stacks 0G5U "first face on nested Finsupp-supported sums"]
theorem face.one.nestedFinsupp {R : Type u} [Ring R] (M : ModuleCat R)
    {ι : Type uι} {κ : ι → Type uκ} (r : ι →₀ R) (s : ∀ i, κ i →₀ R)
    (m : ∀ i, κ i → M) :
    (face R 0 (0 : Fin 2)).app M
        (r.sum fun i a => a • ModuleCat.freeMk
          ((s i).sum fun j b => b • ModuleCat.freeMk (m i j))) =
      r.sum fun i a => a • ModuleCat.freeMk
        ((s i).sum fun j b => b • m i j) := sorry

/-- The zeroth degeneracy adds an outer bracket to a nested finitely supported expression. -/
@[stacks 0G5U "zeroth degeneracy on nested Finsupp-supported sums"]
theorem degeneracy.zero.nestedFinsupp {R : Type u} [Ring R] (M : ModuleCat R)
    {ι : Type uι} {κ : ι → Type uκ} (r : ι →₀ R) (s : ∀ i, κ i →₀ R)
    (m : ∀ i, κ i → M) :
    (degeneracy R 1 (1 : Fin 2)).app M
        (r.sum fun i a => a • ModuleCat.freeMk
          ((s i).sum fun j b => b • ModuleCat.freeMk (m i j))) =
      r.sum fun i a => a • ModuleCat.freeMk
        (ModuleCat.freeMk ((s i).sum fun j b => b • ModuleCat.freeMk (m i j))) := sorry

/-- The first degeneracy brackets every inner generator in a nested finitely supported expression. -/
@[stacks 0G5U "first degeneracy on nested Finsupp-supported sums"]
theorem degeneracy.one.nestedFinsupp {R : Type u} [Ring R] (M : ModuleCat R)
    {ι : Type uι} {κ : ι → Type uκ} (r : ι →₀ R) (s : ∀ i, κ i →₀ R)
    (m : ∀ i, κ i → M) :
    (degeneracy R 1 (0 : Fin 2)).app M
        (r.sum fun i a => a • ModuleCat.freeMk
          ((s i).sum fun j b => b • ModuleCat.freeMk (m i j))) =
      r.sum fun i a => a • ModuleCat.freeMk
        ((s i).sum fun j b => b • ModuleCat.freeMk (ModuleCat.freeMk (m i j))) := sorry

end CategoryTheory.ModuleCat.FreeForgetResolution
