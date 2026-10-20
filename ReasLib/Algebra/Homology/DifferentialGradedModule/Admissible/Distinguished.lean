/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Admissible.Triangle
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Triangulated

/-!
# Distinguished Triangles from Admissible DG-Module Sequences

The intrinsic triangulated structure is canonically owned by mapping-cone triangles.  This leaf
relates that owner to the textbook presentation by admissible short exact sequences, without
introducing a second distinguished-triangle family.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Pretriangulated DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedModule.ShortComplex

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}

/-- A triangle is associated to a short complex when it is isomorphic to the triangle obtained
from some graded `A`-linear splitting of that short complex. -/
def IsAssociatedTriangle
    (S : CategoryTheory.ShortComplex (DifferentialGradedModule.{u, w} A))
    (T : Triangle (K R (DifferentialGradedModule.{u, w} A))) : Prop :=
  ∃ sigma : GradedSplitting S, Nonempty (T ≅ associatedTriangleK S sigma)

/-- Once a graded splitting is fixed, being associated to `S` is equivalent to being isomorphic
to the triangle obtained from that splitting. -/
theorem isAssociatedTriangle_iff_iso
    (S : CategoryTheory.ShortComplex (DifferentialGradedModule.{u, w} A))
    (T : Triangle (K R (DifferentialGradedModule.{u, w} A)))
    (sigma : GradedSplitting S) :
    IsAssociatedTriangle S T ↔ Nonempty (T ≅ associatedTriangleK S sigma) := sorry

end DifferentialGradedModule.ShortComplex

namespace DifferentialGradedModule.Homotopy

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}

/-- Definition 22.8.2 (09K8): a triangle in the intrinsic DG homotopy category is distinguished
exactly when it is associated to an admissible short exact sequence of DG modules. -/
@[stacks 09K8 "distinguished triangles from admissible DG-module short exact sequences"]
theorem distinguished_iff_associated
    (T : Triangle (K R (DifferentialGradedModule.{u, w} A))) :
    T ∈ distTriang (K R (DifferentialGradedModule.{u, w} A)) ↔
      ∃ S : CategoryTheory.ShortComplex (DifferentialGradedModule.{u, w} A),
        IsAdmissibleShortExact S ∧ ShortComplex.IsAssociatedTriangle S T := sorry

end DifferentialGradedModule.Homotopy
