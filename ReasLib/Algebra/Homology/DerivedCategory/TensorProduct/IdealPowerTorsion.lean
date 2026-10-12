/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import ReasLib.Algebra.Homology.DerivedCategory.TensorProduct
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
import ReasLib.Algebra.Homology.ChainComplex.IdealPowerResolution
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived tensor products with ideal-power torsion

This file owns the nonpositive cohomological bounds and zero-object criteria obtained by
tensoring with ideal-power torsion modules and bounded derived objects.

@stack 0H82
@stack 0G1T
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedTensorProduct

universe u

namespace CategoryTheory.DerivedCategory.TensorProduct.IdealPowerTorsion

section

variable {R : Type u} [CommRing R] (I : Ideal R)

local notation "DMod" => _root_.DerivedCategory (ModuleCat R)
local notation "H" => _root_.DerivedCategory.homologyFunctor (ModuleCat R)
local notation "RmodI" => ModuleCat.single0Functor.obj (ModuleCat.of R (R ⧸ I))

/-- Lemma 15.89.7 (1): if tensoring `K` with `R ⧸ I` has no positive cohomology, the
same holds after tensoring with `R ⧸ Iⁿ` for every positive `n`. -/
@[stacks 0H82 "Lemma 15.89.7 (1)"]
theorem quotient_isLE_zero
    (K : DMod) (hKI : (K ⊗[R]^L RmodI).IsLE 0) (n : ℕ+) :
    (K ⊗[R]^L ModuleCat.single0Functor.obj
      (ModuleCat.of R (R ⧸ I ^ (n : ℕ)))).IsLE 0 := sorry
-- Proof strategy: induct on the positive exponent using the short exact filtration of
-- `R ⧸ I ^ n` whose successive quotients are modules over `R ⧸ I`, and use triangulated
-- closure of `IsLE 0`.

/-- Lemma 15.89.7 (2): the same nonpositive bound holds after tensoring with any
`I`-power torsion module. -/
@[stacks 0H82 "Lemma 15.89.7 (2)"]
theorem module_isLE_zero
    (K : DMod) (hKI : (K ⊗[R]^L RmodI).IsLE 0)
    (N : ModuleCat R) (hN : Module.IsIdealPowerTorsion I N) :
    (K ⊗[R]^L ModuleCat.single0Functor.obj N).IsLE 0 := sorry
-- Proof strategy: resolve `N` by direct sums of positive ideal-power quotients via
-- `ChainComplex.IdealPowerResolution.exists_resolution`, apply `quotient_isLE_zero`
-- termwise, and pass the bound through the derived realization.

/-- A reusable form of the bounded-complex clause in which torsion is required only in
nonpositive degrees; the `IsLE 0` hypothesis already forces positive cohomology to vanish. -/
@[stacks 0H82 "bounded nonpositive torsion companion"]
theorem bounded_isLE_zero_of_nonpositive
    (K : DMod) (hKI : (K ⊗[R]^L RmodI).IsLE 0)
    (M : _root_.DerivedCategory.Bounded (ModuleCat R))
    (hMtors : ∀ i ≤ 0, Module.IsIdealPowerTorsion I ((H i).obj M.obj))
    (hMle : M.obj.IsLE 0) :
    (K ⊗[R]^L M.obj).IsLE 0 := sorry
-- Proof strategy: truncate the bounded object and induct along its finite Postnikov tower;
-- apply `module_isLE_zero` to every nonpositive cohomology object.

/-- Lemma 15.89.7 (3): if `M ∈ Dᵇ(R)` has `I`-power torsion cohomology and no positive
cohomology, then `K ⊗ᴸ_R M` has no positive cohomology. -/
@[stacks 0H82 "Lemma 15.89.7 (3)"]
theorem bounded_isLE_zero
    (K : DMod) (hKI : (K ⊗[R]^L RmodI).IsLE 0)
    (M : _root_.DerivedCategory.Bounded (ModuleCat R))
    (hMtors : ∀ i : ℤ, Module.IsIdealPowerTorsion I ((H i).obj M.obj))
    (hMle : M.obj.IsLE 0) :
    (K ⊗[R]^L M.obj).IsLE 0 := sorry
-- Proof strategy: apply `bounded_isLE_zero_of_nonpositive`, restricting `hMtors` to
-- nonpositive degrees.

/-- Lemma 15.89.8 (1): if `K ⊗ᴸ_R (R ⧸ I)` is zero, then
`K ⊗ᴸ_R (R ⧸ Iⁿ)` is zero for every positive `n`. -/
@[stacks 0G1T "Lemma 15.89.8 (1)"]
theorem quotient_isZero
    (K : DMod) (hKI : IsZero (K ⊗[R]^L RmodI)) (n : ℕ+) :
    IsZero (K ⊗[R]^L ModuleCat.single0Functor.obj
      (ModuleCat.of R (R ⧸ I ^ (n : ℕ)))) := sorry
-- Proof strategy: repeat the ideal-power filtration used by `quotient_isLE_zero`; tensoring
-- each successive `R ⧸ I`-module quotient is zero, so every extension is zero.

/-- Lemma 15.89.8 (2): if `K ⊗ᴸ_R (R ⧸ I)` is zero, then `K ⊗ᴸ_R N` is
zero for every `I`-power torsion module `N`. -/
@[stacks 0G1T "Lemma 15.89.8 (2)"]
theorem module_isZero
    (K : DMod) (hKI : IsZero (K ⊗[R]^L RmodI))
    (N : ModuleCat R) (hN : Module.IsIdealPowerTorsion I N) :
    IsZero (K ⊗[R]^L ModuleCat.single0Functor.obj N) := sorry
-- Proof strategy: use the ideal-power quotient resolution of `N`, apply `quotient_isZero`
-- to every term, and identify the derived tensor of the resulting acyclic model.

/-- Lemma 15.89.8 (3): if `K ⊗ᴸ_R (R ⧸ I)` is zero, then `K ⊗ᴸ_R M` is
zero for every bounded derived object `M` whose cohomology is `I`-power torsion. -/
@[stacks 0G1T "Lemma 15.89.8 (3)"]
theorem bounded_isZero
    (K : DMod) (hKI : IsZero (K ⊗[R]^L RmodI))
    (M : _root_.DerivedCategory.Bounded (ModuleCat R))
    (hMtors : ∀ i : ℤ, Module.IsIdealPowerTorsion I ((H i).obj M.obj)) :
    IsZero (K ⊗[R]^L M.obj) := sorry
-- Proof strategy: induct over the finite cohomological amplitude of `M`; each Postnikov
-- layer is zero after tensoring by `module_isZero`.

end

end CategoryTheory.DerivedCategory.TensorProduct.IdealPowerTorsion
