/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Crystalline.SmoothLift.DeRham
public import stacks_project.Chap60.Remark_60_24_11_Comparison_Object
public import stacks_project.Chap60.Remark_60_24_11_Comparison_DeRham
public import stacks_project.Chap60.Remark_60_24_11_Comparison_AffineSections
public import stacks_project.Chap60.Remark_60_24_11_Comparison_AffineDifferentials
public import stacks_project.Chap60.Remark_60_24_11_Comparison_AffineTensorSections
public import stacks_project.Chap60.Remark_60_24_11_Comparison_AffineSheafExtension

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace CrystallineSmoothLiftAffine
export AlgebraicGeometry.Scheme.Crystalline.SmoothLift.Affine (chartAlgebra chart fibre fibre_open square ideal_nil object
  object_baseCompatible smallObject toWhole coefficientComparison coefficientIso
  coefficientSectionsIso coefficientModule coefficientSectionsEquiv tensorToSections
  tensorToSections_bijective connection complex tensorSectionsEquiv termSectionsEquiv
  localDifferential sheafTerm localLinearDifferential basisDifferential sheafDifferential
  sheafDifferential_affine sheafDifferential_comp sheafComplex)
end CrystallineSmoothLiftAffine
variable {Y : Scheme.{u}} (U : Y.affineOpens)
#check (AlgebraicGeometry.Scheme.Crystalline.SmoothLift.Affine.chart U : Spec (.of Γ(Y, U.1)) ⟶ Y)
