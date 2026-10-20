module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap108.Lemma_108_5_1_ClosedImmersion
public import stacks_project.Chap108.Lemma_108_5_6_Map
public import stacks_project.Chap108.Remark_108_5_9_Numerical_invariants_Locus
import StacksCheckRecall

/-!
# Remark 108.5.9 (Numerical invariants)

The forgetful `T`-point map `Quot_{F/X/B} ⟶ Coh_{X/B}` and the numerical
locus `Quot^P_{F/X/B}` as a subfunctor of `quot`. The inclusion is a flat
closed immersion, and an open immersion if `I` is finite, or `B` is locally
Noetherian, or the family is `n ↦ L^{⊗ n}` for invertible `L`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Quot
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/- Remark 108.5.9 (Numerical invariants) (1) -/
@[stacks 0DP6] #check QuotPoint.toObj

/- Remark 108.5.9 (Numerical invariants) (2) -/
@[stacks 0DP6] #check quotNumerical

/-- Remark 108.5.9 (Numerical invariants) (3): the inclusion
`Quot^P_{F/X/B} ⟶ Quot_{F/X/B}` is a closed immersion. -/
@[stacks 0DP6]
theorem isClosedImmersion_quotNumericalι (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (F : X.Modules) [F.IsQuasicoherent] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    IsClosedImmersionOnSchemesOver (quotNumericalι f F E P hE) :=
  sorry

/-- Remark 108.5.9 (Numerical invariants) (4): the inclusion
`Quot^P_{F/X/B} ⟶ Quot_{F/X/B}` is flat. -/
@[stacks 0DP6]
theorem isFlat_quotNumericalι (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (F : X.Modules) [F.IsQuasicoherent] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    IsFlatOnSchemesOver (quotNumericalι f F E P hE) :=
  sorry

/-- Remark 108.5.9 (Numerical invariants) (5): if `I` is finite, then the
inclusion `Quot^P_{F/X/B} ⟶ Quot_{F/X/B}` is an open immersion. -/
@[stacks 0DP6]
theorem isOpenImmersion_quotNumericalι_of_finite (f : X ⟶ B)
    [FinitePresentation f] [Separated f] (F : X.Modules) [F.IsQuasicoherent]
    {I : Type u} [Finite I] (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    IsOpenImmersionOnSchemesOver (quotNumericalι f F E P hE) :=
  sorry

/-- Remark 108.5.9 (Numerical invariants) (6): if `B` is locally Noetherian,
then the inclusion `Quot^P_{F/X/B} ⟶ Quot_{F/X/B}` is an open immersion. -/
@[stacks 0DP6]
theorem isOpenImmersion_quotNumericalι_of_locallyNoetherian (f : X ⟶ B)
    [FinitePresentation f] [Separated f] (F : X.Modules) [F.IsQuasicoherent]
    {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i))
    [AlgebraicSpace.IsLocallyNoetherian B] :
    IsOpenImmersionOnSchemesOver (quotNumericalι f F E P hE) :=
  sorry

/-- Remark 108.5.9 (Numerical invariants) (7): if `E n = L^{⊗ n}` for an
invertible `𝒪_X`-module `L`, then the inclusion
`Quot^{P,L}_{F/X/B} ⟶ Quot_{F/X/B}` is an open immersion. -/
@[stacks 0DP6]
theorem isOpenImmersion_quotNumericalHilbertι (f : X ⟶ B)
    [FinitePresentation f] [Separated f] (F L : X.Modules)
    [F.IsQuasicoherent] [isInvertibleObject L] (P : ℤ → ℤ) :
    IsOpenImmersionOnSchemesOver
      (quotNumericalι f F (invertiblePowerFamily L)
        (fun n : ULift.{u, 0} ℤ ↦ P n.down) (isPerfect_invertiblePowerFamily L)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
