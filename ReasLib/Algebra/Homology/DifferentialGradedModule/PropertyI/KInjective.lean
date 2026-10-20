/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy.Orthogonal
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyI.Milnor

/-!
# Property I modules are K-injective
-/

@[expose] public section

universe u v

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedModule.HasPropertyI

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}

/-- A right DG module with property I is K-injective in the intrinsic homotopy category. -/
@[stacks 09KS "property-I modules are K-injective"]
theorem kInjective {I : DifferentialGradedModule.{u, v} A} (hI : HasPropertyI A I) :
    Homotopy.kInjective A ((toK A).obj I) := sorry

/-- Lemma 22.21.2 (09KS): every morphism from an acyclic right DG module to a property I
module is zero in the intrinsic homotopy category. -/
@[stacks 09KS]
theorem hom_eq_zero_of_acyclic {N I : DifferentialGradedModule.{u, v} A}
    (hI : HasPropertyI A I) (hN : Homotopy.acyclic A ((toK A).obj N))
    (f : (toK A).obj N ⟶ (toK A).obj I) : f = 0 := sorry

end DifferentialGradedModule.HasPropertyI
