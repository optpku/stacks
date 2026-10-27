/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Numerical
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Representability
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.OpenImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver.MorphismProperty
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian

/-! # Geometric properties of numerical Quot loci -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The inclusion
`Quot^P_{F/X/B} ⟶ Quot_{F/X/B}` is a closed immersion. -/
theorem isClosedImmersion_quotNumericalι (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (F : X.Modules) [F.IsQuasicoherent] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    SchemeOver.IsClosedImmersion (quotNumericalι f F E P hE) := sorry

/-- The inclusion
`Quot^P_{F/X/B} ⟶ Quot_{F/X/B}` is flat. -/
theorem isFlat_quotNumericalι (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (F : X.Modules) [F.IsQuasicoherent] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    SchemeOver.IsFlat (quotNumericalι f F E P hE) := sorry

/-- If `I` is finite, then the
inclusion `Quot^P_{F/X/B} ⟶ Quot_{F/X/B}` is an open immersion. -/
theorem isOpenImmersion_quotNumericalι_of_finite (f : X ⟶ B)
    [FinitePresentation f] [Separated f] (F : X.Modules) [F.IsQuasicoherent]
    {I : Type u} [Finite I] (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    IsOpenImmersionOnSchemesOver (quotNumericalι f F E P hE) := sorry

/-- If `B` is locally Noetherian,
then the inclusion `Quot^P_{F/X/B} ⟶ Quot_{F/X/B}` is an open immersion. -/
theorem isOpenImmersion_quotNumericalι_of_locallyNoetherian (f : X ⟶ B)
    [FinitePresentation f] [Separated f] (F : X.Modules) [F.IsQuasicoherent]
    {I : Type u} (E : I → ModuleDerived X) (P : I → ℤ)
    (hE : ∀ i, ModuleDerived.IsPerfect (E i))
    [AlgebraicSpace.IsLocallyNoetherian B] :
    IsOpenImmersionOnSchemesOver (quotNumericalι f F E P hE) := sorry

/-- If `E n = L^{⊗ n}` for an
invertible `𝒪_X`-module `L`, then the inclusion
`Quot^{P,L}_{F/X/B} ⟶ Quot_{F/X/B}` is an open immersion. -/
theorem isOpenImmersion_quotNumericalHilbertι (f : X ⟶ B)
    [FinitePresentation f] [Separated f] (F L : X.Modules)
    [F.IsQuasicoherent] [isInvertibleObject L] (P : ℤ → ℤ) :
    IsOpenImmersionOnSchemesOver
      (quotNumericalι f F (invertiblePowerFamily L)
        (fun n : ULift.{u, 0} ℤ ↦ P n.down) (isPerfect_invertiblePowerFamily L)) := sorry

/-- The numerical locus of the proper-support Quot functor is an algebraic space over the base. -/
theorem quotNumerical_isAlgebraicSpaceOver (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (F : X.Modules) [F.IsQuasicoherent] {I : Type u}
    (E : I → ModuleDerived X) (P : I → ℤ) (hE : ∀ i, ModuleDerived.IsPerfect (E i)) :
    IsAlgebraicSpaceOver (quotNumerical f F E P hE).toFunctor := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
