/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.Tensor.Comparison

/-!
# Compatibility facade for Lemma 27.9.1 tensor infrastructure

The reusable tensor grading lives in `ReasLib.Algebra.Module.Graded.TensorProduct.NatInt`;
the associated-sheaf morphism and local comparison squares live in the associated-module tensor
module.
-/

@[expose] public section

#check @GradedModule.TensorProduct.grading
#check @GradedModule.TensorProduct.gradingFor
#check AlgebraicGeometry.Proj.AssociatedModule.Tensor.hom
#check AlgebraicGeometry.Proj.AssociatedModule.Tensor.globalSections
#check AlgebraicGeometry.Proj.AssociatedModule.Tensor.away
#check AlgebraicGeometry.Proj.AssociatedModule.Tensor.stalk
