/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Covers of ideal-power torsion modules

An ideal-power torsion module has a canonical cover indexed by an element together with a
positive ideal power annihilating it.  Each summand is the corresponding quotient `R ⧸ I ^ n`.
Using all witnesses makes the data canonical and avoids a public choice of annihilating exponent.
@stack 05E8
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped DirectSum

universe u

namespace ModuleCat.IdealPower.Cover

variable {R : Type u} [CommRing R]

/-- Lemma 15.89.2 (Tag 05E8): indices for the canonical quotient cover, consisting of a positive
power and an element annihilated by that power. -/
@[stacks 05E8 "canonical ideal-power quotient cover indices"]
abbrev Index (I : Ideal R) (M : ModuleCat.{u} R) :=
  Σ n : ℕ+, Ideal.powerTorsion I M (n : ℕ)

/-- A canonical classical equality decision for the cover's sigma index. -/
noncomputable instance indexDecidableEq (I : Ideal R) (M : ModuleCat.{u} R) :
    DecidableEq (Index I M) := Classical.decEq _

/-- Lemma 15.89.2 (Tag 05E8): the direct sum of positive ideal-power quotients indexed by all
annihilation witnesses in `M`. -/
@[stacks 05E8 "canonical ideal-power quotient cover source"]
abbrev source (I : Ideal R) (M : ModuleCat.{u} R) : ModuleCat.{u} R :=
  ModuleCat.of R (⨁ p : Index I M, R ⧸ I ^ (p.1 : ℕ))

/-- The ideal defining a cover summand lies in the kernel of scalar multiplication by its
indexed element. -/
@[stacks 05E8 "annihilation relation for ideal-power cover summands"]
theorem pow_le_ker_toSpanSingleton (I : Ideal R) (M : ModuleCat.{u} R)
    (p : Index I M) :
    (I ^ (p.1 : ℕ) : Ideal R) ≤
      LinearMap.ker (LinearMap.toSpanSingleton R M p.2.1) := by
  intro a ha
  rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
  exact (Submodule.mem_torsionBySet_iff (R := R) (M := M)
    (s := ((I ^ (p.1 : ℕ) : Ideal R) : Set R)) p.2.1).mp p.2.2 ⟨a, ha⟩

/-- The canonical map from the quotient summand indexed by `p` to its distinguished scalar
multiples in `M`. -/
@[stacks 05E8 "ideal-power quotient cover summand map"]
def summandMap (I : Ideal R) (M : ModuleCat.{u} R) (p : Index I M) :
    R ⧸ I ^ (p.1 : ℕ) →ₗ[R] M :=
  (I ^ (p.1 : ℕ)).liftQ (LinearMap.toSpanSingleton R M p.2.1)
    (pow_le_ker_toSpanSingleton I M p)

/-- The linear map assembled from all canonical quotient summands. -/
@[stacks 05E8 "canonical ideal-power quotient cover map"]
def linearMap (I : Ideal R) (M : ModuleCat.{u} R) :
    (⨁ p : Index I M, R ⧸ I ^ (p.1 : ℕ)) →ₗ[R] M :=
  DirectSum.toModule R (Index I M) M (summandMap I M)

/-- Lemma 15.89.2 (Tag 05E8): the canonical morphism from the direct sum of ideal-power
quotients to the torsion module. -/
@[stacks 05E8 "canonical ideal-power quotient cover"]
def π (I : Ideal R) (M : ModuleCat.{u} R) : source I M ⟶ M :=
  ModuleCat.ofHom (linearMap I M)

/-- The inclusion of one quotient summand into the canonical cover source. -/
@[stacks 05E8 "canonical ideal-power quotient summand inclusion"]
def ι (I : Ideal R) (M : ModuleCat.{u} R) (p : Index I M) :
    ModuleCat.of R (R ⧸ I ^ (p.1 : ℕ)) ⟶ source I M :=
  ModuleCat.ofHom
    (DirectSum.lof R (Index I M) (fun q ↦ R ⧸ I ^ (q.1 : ℕ)) p)

/-- The canonical summand map sends the class of `r` to `r • p`. -/
@[stacks 05E8 "quotient representative formula for cover summands", simp]
theorem summandMap_mk (I : Ideal R) (M : ModuleCat.{u} R)
    (p : Index I M) (r : R) :
    summandMap I M p (Ideal.Quotient.mk (I ^ (p.1 : ℕ)) r) = r • p.2.1 := sorry

/-- The cover morphism restricts to the canonical map on every direct-sum component. -/
@[stacks 05E8 "cover map on quotient summands", reassoc (attr := simp)]
theorem ι_π (I : Ideal R) (M : ModuleCat.{u} R) (p : Index I M) :
    ι I M p ≫ π I M = ModuleCat.ofHom (summandMap I M p) := sorry

/-- The source of the canonical quotient cover is ideal-power torsion. -/
@[stacks 05E8 "torsion of the canonical ideal-power quotient cover"]
theorem source_torsion (I : Ideal R) (M : ModuleCat.{u} R) :
    Module.IsIdealPowerTorsion I (source I M) := sorry

/-- Lemma 15.89.2 (Tag 05E8): the canonical quotient cover is an epimorphism for an
ideal-power torsion module. -/
@[stacks 05E8 "canonical ideal-power quotient cover is epi"]
theorem π_epi (I : Ideal R) {M : ModuleCat.{u} R}
    (hM : Module.IsIdealPowerTorsion I M) : Epi (π I M) := sorry

/-- The kernel of the canonical quotient cover remains ideal-power torsion. -/
@[stacks 05E8 "torsion kernel of the canonical ideal-power quotient cover"]
theorem kernel_torsion (I : Ideal R) (M : ModuleCat.{u} R) :
    Module.IsIdealPowerTorsion I (kernel (π I M) : ModuleCat.{u} R) := sorry

end ModuleCat.IdealPower.Cover
