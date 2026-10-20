/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy.Orthogonal
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.Telescope

/-!
# Property P modules are K-projective
-/

@[expose] public section

universe u v

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedModule.HasPropertyP

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}

/-- A right DG module with property P is K-projective in the intrinsic homotopy category. -/
@[stacks 09KM "property-P modules are K-projective"]
theorem kProjective {P : DifferentialGradedModule.{u, v} A} (hP : HasPropertyP A P) :
    Homotopy.kProjective A ((toK A).obj P) := sorry

/-- Lemma 22.20.2 (09KM): every morphism from a property P right DG module to an acyclic right
DG module is zero in the intrinsic homotopy category. -/
@[stacks 09KM]
theorem hom_eq_zero_of_acyclic {P N : DifferentialGradedModule.{u, v} A}
    (hP : HasPropertyP A P) (hN : Homotopy.acyclic A ((toK A).obj N))
    (f : (toK A).obj P ⟶ (toK A).obj N) : f = 0 := sorry

end DifferentialGradedModule.HasPropertyP
