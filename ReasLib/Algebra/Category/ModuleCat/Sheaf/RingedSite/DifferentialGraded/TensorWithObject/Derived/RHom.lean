/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Derived.Hom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Derived.Hom.Cohomology
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Derived.Hom.Model

/-!
# Compatibility import for the tensor-Hom comparison

The abstract source and target bifunctors and the property-(P)/K-injective computation model now
live in `TensorWithObject.Derived.Hom`. The generic operation of right-deriving a mapped Hom
bifunctor remains in `DifferentialGradedCategory.HomComplex.Derived.RightDerivedMap` and is not
the 0CS6 target.

This former ringed-site path remains as a compatibility import for downstream files. New code
should import `TensorWithObject.Derived.Hom` or its `Hom.Model` leaf directly.
-/
