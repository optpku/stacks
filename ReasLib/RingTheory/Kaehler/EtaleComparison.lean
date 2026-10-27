/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Etale.Kaehler
public import ReasLib.RingTheory.Kaehler.Unramified

/-!
# Canonical differential comparison for an étale square

The source-change equivalence uses the proved transitivity sequence in
`Unramified`. Composing it with formally étale base change gives the comparison
for two compatible algebra towers, without a Cartesian hypothesis.
-/

@[expose] public section

open scoped TensorProduct

universe u v w z

namespace KaehlerDifferential

section SourceChange

variable (R : Type u) (Rprime : Type v) (Bprime : Type w)
variable [CommRing R] [CommRing Rprime] [CommRing Bprime]
variable [Algebra R Rprime] [Algebra R Bprime] [Algebra Rprime Bprime]
variable [IsScalarTower R Rprime Bprime]
variable [Algebra.FormallyUnramified R Rprime]

/-- Changing a formally unramified source preserves the differential module. -/
noncomputable def mapEquivOfFormallyUnramified :
    Ω[Bprime⁄R] ≃ₗ[Bprime] Ω[Bprime⁄Rprime] :=
  LinearEquiv.ofBijective (map R Rprime Bprime Bprime)
    (map_bijective_of_formallyUnramified (R := R) (S := Rprime) (T := Bprime))

/-- The equivalence has the canonical source-change map as its forward map. -/
@[simp] theorem mapEquivOfFormallyUnramified_apply (x : Ω[Bprime⁄R]) :
    mapEquivOfFormallyUnramified R Rprime Bprime x = map R Rprime Bprime Bprime x := rfl

/-- The actual inverse cancels the canonical source-change map. -/
@[simp] theorem mapEquivOfFormallyUnramified_symm_apply_map (x : Ω[Bprime⁄R]) :
    (mapEquivOfFormallyUnramified R Rprime Bprime).symm
      (map R Rprime Bprime Bprime x) = x := by
  change (mapEquivOfFormallyUnramified R Rprime Bprime).symm
    (mapEquivOfFormallyUnramified R Rprime Bprime x) = x
  exact (mapEquivOfFormallyUnramified R Rprime Bprime).symm_apply_apply x

end SourceChange

section Square

variable (R : Type u) (B : Type v) (Rprime : Type w) (Bprime : Type z)
variable [CommRing R] [CommRing B] [CommRing Rprime] [CommRing Bprime]
variable [Algebra R B] [Algebra R Rprime] [Algebra B Bprime]
variable [Algebra Rprime Bprime] [Algebra R Bprime]
variable [IsScalarTower R B Bprime] [IsScalarTower R Rprime Bprime]
variable [Algebra.FormallyUnramified R Rprime] [Algebra.FormallyEtale B Bprime]

/-- Formally étale target change followed by formally unramified source change. -/
noncomputable def etaleSquareEquiv :
    Bprime ⊗[B] Ω[B⁄R] ≃ₗ[Bprime] Ω[Bprime⁄Rprime] :=
  (tensorKaehlerEquivOfFormallyEtale R B Bprime).trans
    (mapEquivOfFormallyUnramified R Rprime Bprime)

/-- The forward comparison is the composite of the two canonical linear maps. -/
theorem etaleSquareEquiv_toLinearMap :
    (etaleSquareEquiv R B Rprime Bprime).toLinearMap =
      (map R Rprime Bprime Bprime).comp (mapBaseChange R B Bprime) := rfl

/-- The comparison sends a differential generator to its canonical image. -/
@[simp] theorem etaleSquareEquiv_apply_tmul_D (b : B) :
    etaleSquareEquiv R B Rprime Bprime (1 ⊗ₜ[B] D R B b) =
      D Rprime Bprime (algebraMap B Bprime b) := by
  change map R Rprime Bprime Bprime
    (mapBaseChange R B Bprime (1 ⊗ₜ[B] D R B b)) = _
  rw [mapBaseChange_tmul, one_smul, map_D, map_D]
  simp only [Algebra.algebraMap_self_apply]

/-- The inverse returns the tensor generator from its differential image. -/
@[simp] theorem etaleSquareEquiv_symm_apply_D (b : B) :
    (etaleSquareEquiv R B Rprime Bprime).symm
      (D Rprime Bprime (algebraMap B Bprime b)) = 1 ⊗ₜ[B] D R B b := by
  rw [← etaleSquareEquiv_apply_tmul_D R B Rprime Bprime b]
  exact (etaleSquareEquiv R B Rprime Bprime).symm_apply_apply _

end Square

end KaehlerDifferential
