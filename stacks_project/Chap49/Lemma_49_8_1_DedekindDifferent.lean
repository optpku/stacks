module

public import ReasLib.RingTheory.DedekindDifferent.TraceDual

@[expose] public section

universe u v w x

section Complementary

variable (A : Type u) (K : Type w) (B : Type v) (L : Type x)
variable [CommRing A] [CommRing K] [CommRing B] [CommRing L]
variable [algAK : Algebra A K] [algAB : Algebra A B]
variable [algBL : Algebra B L] [algKL : Algebra K L] [algAL : Algebra A L]
variable [towerAKL : IsScalarTower A K L] [towerABL : IsScalarTower A B L]

/- The complementary module is provided by its reusable mathematical owner. -/
#check (Submodule.dedekindComplementary A K B L : Submodule B L)

/- The membership characterization of the complementary module is publicly re-exported. -/
#check (Submodule.mem_dedekindComplementary_iff A K B L : ∀ x : L,
    x ∈ Submodule.dedekindComplementary A K B L ↔
      ∀ b : B, Algebra.trace K L (algebraMap B L b * x) ∈
        (algebraMap A K).range)

/- The Dedekind different is provided by its reusable mathematical owner. -/
#check (Submodule.dedekindDifferent A K B L : Submodule B L)

/- The membership characterization of the Dedekind different is publicly re-exported. -/
#check (Submodule.mem_dedekindDifferent_iff A K B L : ∀ x : L,
    x ∈ Submodule.dedekindDifferent A K B L ↔
      ∀ y ∈ Submodule.dedekindComplementary A K B L,
        x * y ∈ (1 : Submodule B L))

end Complementary

section TraceDual

variable (A : Type u) (K : Type w) (B : Type v) (L : Type x)
variable [CommRing A] [Field K] [CommRing B] [Field L]
variable [Algebra A K] [Algebra A B] [Algebra B L] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L]

/- The identification of the complementary module with Mathlib's trace dual is re-exported. -/
#check (Submodule.dedekindComplementary_eq_traceDual A K B L :
  Submodule.dedekindComplementary A K B L =
    Submodule.traceDual A K (1 : Submodule B L))

end TraceDual
