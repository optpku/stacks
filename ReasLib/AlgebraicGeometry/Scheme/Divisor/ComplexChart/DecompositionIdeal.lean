/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.Decomposition
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ComplexChart

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DivisorComplexChart

/-- The total Berthelot–Ogus decomposition ideal attached to a divisor-complex chart. -/
noncomputable def decompositionIdeal {X : Scheme.{u}} {D : X.IdealSheafData}
    {M : RingedSpace.ModuleDerived X.toRingedSpace} (C : DivisorComplexChart D M) :
    Ideal (Γ(X, C.U) ⧸ Ideal.span {C.generator}) :=
  @CochainComplex.BerthelotOgus.Int.Reduction.Decomposition.ideal
    _ _ ⟨C.generator, C.regular⟩ C.model C.finiteFree

/-- The chart decomposition ideal is the canonical sum of the degreewise decomposition
ideals of its finite-free model. -/
theorem decompositionIdeal_def {X : Scheme.{u}} {D : X.IdealSheafData}
    {M : RingedSpace.ModuleDerived X.toRingedSpace} (C : DivisorComplexChart D M) :
    C.decompositionIdeal =
      @CochainComplex.BerthelotOgus.Int.Reduction.Decomposition.ideal
        _ _ ⟨C.generator, C.regular⟩ C.model C.finiteFree := sorry

/-- The restriction of an ideal sheaf on the divisor, transported to the quotient ring of a
divisor-complex chart. -/
noncomputable def restrictIdeal {X : Scheme.{u}} {D : X.IdealSheafData}
    {M : RingedSpace.ModuleDerived X.toRingedSpace} (C : DivisorComplexChart D M)
    (J : D.subscheme.IdealSheafData) :
    Ideal (Γ(X, C.U) ⧸ Ideal.span {C.generator}) :=
  Ideal.map (Ideal.quotEquivOfEq C.ideal_eq).toRingHom
    (Ideal.map (D.subschemeObjIso C.U).hom.hom
      (J.ideal ⟨D.subschemeι ⁻¹ᵁ C.U, C.U.2.preimage D.subschemeι⟩))

/-- The restricted chart ideal is obtained from divisor sections via `subschemeObjIso`, then
transported along the equality between the divisor ideal and the chart's principal ideal. -/
theorem restrictIdeal_def {X : Scheme.{u}} {D : X.IdealSheafData}
    {M : RingedSpace.ModuleDerived X.toRingedSpace} (C : DivisorComplexChart D M)
    (J : D.subscheme.IdealSheafData) :
    C.restrictIdeal J =
      Ideal.map (Ideal.quotEquivOfEq C.ideal_eq).toRingHom
        (Ideal.map (D.subschemeObjIso C.U).hom.hom
          (J.ideal ⟨D.subschemeι ⁻¹ᵁ C.U, C.U.2.preimage D.subschemeι⟩)) := sorry

end AlgebraicGeometry.Scheme.DivisorComplexChart
