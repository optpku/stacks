module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.Algebra.Category.ModuleCat.Tor.Notation
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Basic

@[expose] public section

noncomputable section

universe u

namespace IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- The maximal ideal annihilates `Tor₁[A](A ⧸ maximalIdeal A ^ n, ResidueField A)`. -/
theorem isTorsionBySet_maximalIdeal_tor_one_quotient_pow (n : ℕ) :
    Module.IsTorsionBySet A (Tor₁[A](A ⧸ maximalIdeal A ^ n, ResidueField A))
      (maximalIdeal A) := sorry

/-- The residue field acts on `Tor₁[A](A ⧸ maximalIdeal A ^ n, ResidueField A)` because the
maximal ideal annihilates this Tor module. -/
instance instModuleResidueField_tor_one_quotient_pow (n : ℕ) :
    Module (ResidueField A) (Tor₁[A](A ⧸ maximalIdeal A ^ n, ResidueField A)) :=
  let hM : Module.IsTorsionBySet A (Tor₁[A](A ⧸ maximalIdeal A ^ n, ResidueField A))
      (maximalIdeal A) := isTorsionBySet_maximalIdeal_tor_one_quotient_pow n
  let smul : SMul (ResidueField A) (Tor₁[A](A ⧸ maximalIdeal A ^ n, ResidueField A)) :=
    ⟨fun b x => (Quotient.out b : A) • x⟩
  let mulAction : MulAction (ResidueField A)
      (Tor₁[A](A ⧸ maximalIdeal A ^ n, ResidueField A)) :=
    { smul := smul.smul
      one_smul := by
        intro x
        change (Quotient.out (1 : ResidueField A) : A) • x = x
        rw [← hM.mk_smul (Quotient.out (1 : ResidueField A)) x]
        have hq : Ideal.Quotient.mk (maximalIdeal A)
            (Quotient.out (1 : ResidueField A)) = 1 :=
          Quotient.out_eq (1 : ResidueField A)
        rw [hq]
        exact hM.module.one_smul x
      mul_smul := by
        intro b c x
        change (Quotient.out (b * c) : A) • x =
          (Quotient.out b : A) • (Quotient.out c : A) • x
        rw [← hM.mk_smul (Quotient.out (b * c)) x]
        rw [← hM.mk_smul (Quotient.out b) ((Quotient.out c : A) • x)]
        rw [← hM.mk_smul (Quotient.out c) x]
        have hbc : Ideal.Quotient.mk (maximalIdeal A) (Quotient.out (b * c)) = b * c :=
          Quotient.out_eq (b * c)
        have hb : Ideal.Quotient.mk (maximalIdeal A) (Quotient.out b) = b := Quotient.out_eq b
        have hc : Ideal.Quotient.mk (maximalIdeal A) (Quotient.out c) = c := Quotient.out_eq c
        rw [hbc, hb, hc]
        exact hM.module.mul_smul b c x }
  let distribMulAction : DistribMulAction (ResidueField A)
      (Tor₁[A](A ⧸ maximalIdeal A ^ n, ResidueField A)) :=
    { toMulAction := mulAction
      smul_zero := by
        intro b
        change (Quotient.out b : A) • (0 : Tor₁[A](A ⧸ maximalIdeal A ^ n, ResidueField A)) = 0
        exact smul_zero _
      smul_add := by
        intro b x y
        change (Quotient.out b : A) • (x + y) = _
        exact smul_add _ _ _ }
  { toDistribMulAction := distribMulAction
    add_smul := by
      intro b c x
      change (Quotient.out (b + c) : A) • x =
        (Quotient.out b : A) • x + (Quotient.out c : A) • x
      rw [← hM.mk_smul (Quotient.out (b + c)) x]
      rw [← hM.mk_smul (Quotient.out b) x]
      rw [← hM.mk_smul (Quotient.out c) x]
      have hbc : Ideal.Quotient.mk (maximalIdeal A) (Quotient.out (b + c)) = b + c :=
        Quotient.out_eq (b + c)
      have hb : Ideal.Quotient.mk (maximalIdeal A) (Quotient.out b) = b := Quotient.out_eq b
      have hc : Ideal.Quotient.mk (maximalIdeal A) (Quotient.out c) = c := Quotient.out_eq c
      rw [hbc, hb, hc]
      exact hM.module.add_smul b c x
    zero_smul := by
      intro x
      change (Quotient.out (0 : ResidueField A) : A) • x = 0
      rw [← hM.mk_smul (Quotient.out (0 : ResidueField A)) x]
      have hz : Ideal.Quotient.mk (maximalIdeal A) (Quotient.out (0 : ResidueField A)) = 0 :=
        Quotient.out_eq (0 : ResidueField A)
      rw [hz]
      exact hM.module.zero_smul x }

/-- For a Noetherian local ring, `Tor₁[A](A ⧸ maximalIdeal A ^ n, ResidueField A)` is
finite-dimensional over the residue field. -/
instance instFiniteDimensional_tor_one_quotient_pow [IsNoetherianRing A] (n : ℕ) :
    FiniteDimensional (ResidueField A)
      (Tor₁[A](A ⧸ maximalIdeal A ^ n, ResidueField A)) := sorry

/-- For a Noetherian local ring and `1 ≤ n`, the residue-field dimension of
`Tor₁[A](A ⧸ maximalIdeal A ^ n, ResidueField A)` equals that of the degree-`n`
associated graded piece of the maximal ideal. -/
theorem finrank_tor_one_quotient_pow_residueField [IsNoetherianRing A] {n : ℕ} (hn : 1 ≤ n) :
    Module.finrank (ResidueField A) (Tor₁[A](A ⧸ maximalIdeal A ^ n, ResidueField A)) =
      Module.finrank (ResidueField A)
        (Ideal.AssociatedGraded.piece (maximalIdeal A) A n) := sorry

end IsLocalRing
