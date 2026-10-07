module

public import ReasLib.RingTheory.Kaehler.BaseChange
public import ReasLib.RingTheory.LocalRing.ResidueField.Kaehler
import Mathlib.Tactic.CrossRefAttribute

/-!
# Residue-field base change for Kaehler differentials

This leaf owns the canonical comparison obtained by taking the
Jacobi-Zariski base-change map to a local ring and then extending scalars to
its residue field.

@stack 07E5
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct
open TensorProduct.AlgebraTensorModule

noncomputable section

universe u v w

namespace KaehlerDifferential

/-- The canonical comparison
`κ(A) ⊗[S] Ω[S⁄R] ⟶ κ(A) ⊗[A] Ω[A⁄R]` induced by
`KaehlerDifferential.mapBaseChange R S A`. -/
@[stacks 07E5 "residue-field Kaehler comparison map"]
noncomputable abbrev residueFieldComparison
    (R : Type u) (S : Type v) (A : Type w)
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra S A] [Algebra R A]
    [IsScalarTower R S A] [IsLocalRing A] :
    ResidueField A ⊗[S] Ω[S⁄R] →ₗ[ResidueField A]
      ResidueField A ⊗[A] Ω[A⁄R] :=
  tensorMapBaseChange R S A (ResidueField A)

/-- Computation of the residue-field comparison on pure tensors. -/
@[simp, stacks 07E5 "residue-field Kaehler comparison on pure tensors"]
theorem residueFieldComparison_tmul
    (R : Type u) (S : Type v) (A : Type w)
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra S A] [Algebra R A]
    [IsScalarTower R S A] [IsLocalRing A]
    (a : ResidueField A) (x : Ω[S⁄R]) :
    residueFieldComparison R S A (a ⊗ₜ[S] x) =
      a ⊗ₜ[A] KaehlerDifferential.map R R S A x :=
  tensorMapBaseChange_tmul R S A (ResidueField A) a x

end KaehlerDifferential
