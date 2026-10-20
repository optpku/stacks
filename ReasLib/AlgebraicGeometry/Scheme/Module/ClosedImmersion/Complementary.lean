module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Complementary
public import ReasLib.AlgebraicGeometry.Scheme.Module.ClosedImmersion.Exact

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.ClosedImmersion

/-- The sum of the ideal-tensor inclusions vanishes after restriction to the
scheme-theoretic intersection. -/
theorem complementaryIdealSum_comp_restriction {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] (F : X.Modules) :
    biprod.desc (idealTensorMap (complementaryClosureι i) F) (idealTensorMap i F) ≫
      restrictionMap (i.ker ⊔ (complementaryClosureι i).ker).subschemeι F = 0 := sorry

/-- The concrete ideal-sum sequence associated to a closed immersion and a module. -/
noncomputable def complementaryIdealSumSequence {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] (F : X.Modules) : ShortComplex X.Modules :=
  ShortComplex.mk
    (biprod.desc (idealTensorMap (complementaryClosureι i) F) (idealTensorMap i F))
    (restrictionMap (i.ker ⊔ (complementaryClosureι i).ker).subschemeι F)
    (complementaryIdealSum_comp_restriction i F)

end AlgebraicGeometry.Scheme.Modules.ClosedImmersion

end
