/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidueField.Morphism.Monomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.GenericPoint

/-!
# Function fields of integral algebraic subspaces

The function field of an integral algebraic space mapped monomorphically into a
decent algebraic space is the residue field at the image of its generic point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Generic-point evaluation followed by the inverse residue-field map identifies
the function field of an integral monomorphic source with the ambient residue field. -/
def rationalFunctionRingEquivResidueFieldOfMono {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    [IsIntegral Y] [IsDecent X] (i : Y ⟶ X) [Mono i]
    {η : Points Y} (hη : η ∈ genericPoints Y) :
    RationalFunction Y ≃+* ULift.{u + 1} (X.residueField (Points.map i η)) :=
  (rationalFunctionRingEquivResidueField hη).trans
    (ULift.ringEquiv.trans
      ((asIso (Hom.residueFieldMap i η)).symm.commRingCatIsoToRingEquiv.trans
        ULift.ringEquiv.symm))

/-- The function-field comparison evaluates at the generic point and then applies
the inverse of the induced residue-field morphism. -/
theorem rationalFunctionRingEquivResidueFieldOfMono_apply {S : Scheme.{u}}
    {Y X : AlgebraicSpace S} [IsIntegral Y] [IsDecent X] (i : Y ⟶ X) [Mono i]
    {η : Points Y} (hη : η ∈ genericPoints Y) (a : RationalFunction Y) :
    rationalFunctionRingEquivResidueFieldOfMono i hη a =
      ULift.up ((asIso (Hom.residueFieldMap i η)).inv
        (rationalFunctionRingEquivResidueField hη a).down) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
