/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.GenericPoint
public import Mathlib.AlgebraicGeometry.FunctionField

@[expose] public section
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) [IsIntegral X]

/-- The canonical residue map identifies the generic stalk with its residue field. -/
def functionFieldResidueEquiv : X.functionField ≃+* X.residueField (genericPoint X) :=
  RingEquiv.ofBijective (X.residue (genericPoint X)).hom
    ⟨(X.residue (genericPoint X)).hom.injective, IsLocalRing.residue_surjective⟩

/-- The generic residue-point morphism factors through the specified residue map. -/
theorem functionFieldResidue_triangle :
    Spec.map (CommRingCat.ofHom (functionFieldResidueEquiv X).toRingHom) ≫
      X.fromSpecStalk (genericPoint X) = X.fromSpecResidueField (genericPoint X) := rfl

/-- The geometric generic point in the separable closure of the function field. -/
def functionFieldGeometricPoint : Spec (.of (SeparableClosure X.functionField)) ⟶ X :=
  separableClosurePoint X.functionField ≫ X.fromSpecStalk (genericPoint X)

/-- The fundamental-group map of the actual generic stalk morphism. -/
def functionFieldFundamentalMap : ContinuousMonoidHom
    (fundamentalGroup (separableClosurePoint X.functionField))
    (fundamentalGroup (functionFieldGeometricPoint X)) :=
  Hom.fundamentalGroupMap (X.fromSpecStalk (genericPoint X))
    (separableClosurePoint X.functionField)

/-- The function-field Galois action followed by the generic stalk morphism. -/
def functionFieldGaloisMap : ContinuousMonoidHom
    Gal(SeparableClosure X.functionField/X.functionField)
    (fundamentalGroup (functionFieldGeometricPoint X)) :=
  (functionFieldFundamentalMap X).comp (fieldGaloisMap X.functionField)

/-- The function-field Galois map factors through its specified field comparison. -/
theorem functionFieldGaloisMap_eq_comp :
    (functionFieldGaloisMap X).toMonoidHom =
      (functionFieldFundamentalMap X).toMonoidHom.comp
        (fieldGaloisEquiv X.functionField).toMonoidHom := rfl

end AlgebraicGeometry.Scheme
