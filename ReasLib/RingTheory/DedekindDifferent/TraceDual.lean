/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.DedekindDomain.Different

@[expose] public section

universe u v w x

section Complementary

variable (A : Type u) (K : Type w) (B : Type v) (L : Type x)
variable [CommRing A] [CommRing K] [CommRing B] [CommRing L]
variable [algAK : Algebra A K] [algAB : Algebra A B]
variable [algBL : Algebra B L] [algKL : Algebra K L] [algAL : Algebra A L]
variable [towerAKL : IsScalarTower A K L] [towerABL : IsScalarTower A B L]

include algAB algAL towerAKL towerABL

/-- The complementary `B`-submodule in `L` defined by the trace pairing over `K`:
`x` belongs precisely when `Algebra.trace K L (b * x)` comes from `A` for every `b : B`. -/
noncomputable def Submodule.dedekindComplementary : Submodule B L where
  carrier := {x | ∀ b : B,
    Algebra.trace K L (algebraMap B L b * x) ∈ (algebraMap A K).range}
  zero_mem' := sorry
  add_mem' := sorry
  smul_mem' := sorry

/-- Membership in the complementary module is exactly the trace-integrality condition. -/
theorem Submodule.mem_dedekindComplementary_iff (x : L) :
    x ∈ Submodule.dedekindComplementary A K B L ↔
      ∀ b : B, Algebra.trace K L (algebraMap B L b * x) ∈
        (algebraMap A K).range := sorry

/-- The Dedekind different is the quotient of the canonical copy of `B` by its
complementary module, viewed as a `B`-submodule of `L`. -/
noncomputable def Submodule.dedekindDifferent : Submodule B L :=
  1 / Submodule.dedekindComplementary A K B L

/-- Membership in the Dedekind different means that multiplication carries the complementary
module into the canonical copy of `B`. -/
theorem Submodule.mem_dedekindDifferent_iff (x : L) :
    x ∈ Submodule.dedekindDifferent A K B L ↔
      ∀ y ∈ Submodule.dedekindComplementary A K B L,
        x * y ∈ (1 : Submodule B L) := sorry

end Complementary

section TraceDual

variable (A : Type u) (K : Type w) (B : Type v) (L : Type x)
variable [CommRing A] [Field K] [CommRing B] [Field L]
variable [Algebra A K] [Algebra A B] [Algebra B L] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L]

/-- The complementary module is the trace dual of the canonical copy of `B` in `L`. -/
theorem Submodule.dedekindComplementary_eq_traceDual :
    Submodule.dedekindComplementary A K B L =
      Submodule.traceDual A K (1 : Submodule B L) := sorry

end TraceDual
