/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NormalizationDegree

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IsDualizingComplex

/- The promoted normalization-degree API is owned by ReasLib. -/
#check IsStalkNormalizationDegreeFunction
#check IsStalkNormalizationDegreeFunction.at
#check normalizationDegree
#check normalizationDegree_spec
#check normalizationDegree_eq
#check normalizationDegree_stalkShift_isNormalized

end AlgebraicGeometry.Scheme.IsDualizingComplex
