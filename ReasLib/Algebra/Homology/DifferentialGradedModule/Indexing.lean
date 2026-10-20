/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra
public import ReasLib.Algebra.Category.ModuleCat.Transport

/-!
# Indexing Operations for Differential Graded Modules

The small cast and index-normalization API is separated from the module
structure so constructions such as shifts and Hom complexes can depend on it
without importing a larger implementation file.
-/

@[expose] public section

noncomputable section

universe u v

variable {R : Type u} [CommRing R]

namespace DifferentialGradedModule

/-- The degree-zero action on `M^p` has target `M^(p + 0)`. -/
theorem zeroActionTarget {M : ℤ → ModuleCat.{v} R} (p : ℤ) :
    (M p : Type v) = M (p + 0) := sorry

/-- Two successive homogeneous actions have target `M^(p + (i + j))`. -/
theorem mulActionTarget {M : ℤ → ModuleCat.{v} R} (p i j : ℤ) :
    (M ((p + i) + j) : Type v) = M (p + (i + j)) := sorry

/-- The first Leibniz summand has target `M^(p + i + 1)`. -/
theorem dLeftActionTarget {M : ℤ → ModuleCat.{v} R} (p i : ℤ) :
    (M ((p + 1) + i) : Type v) = M (p + i + 1) := sorry

/-- The second Leibniz summand has target `M^(p + i + 1)`. -/
theorem dRightActionTarget {M : ℤ → ModuleCat.{v} R} (p i : ℤ) :
    (M (p + (i + 1)) : Type v) = M (p + i + 1) := sorry

end DifferentialGradedModule
