module

public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Graded.Limits
public import ReasLib.CategoryTheory.Preadditive.CompactObject

/-!
# Finite Projective Graded Modules

This leaf owns finite projectivity for the external graded right modules underlying differential
graded modules.  The condition is imposed in the category of graded `A`-modules, so it retains the
graded `A`-action rather than testing the homogeneous pieces only as modules over the ground ring.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)

namespace Graded

/-- Categorical finite generation for an external graded right `A`-module.  This is compactness
in the graded module category, and is deliberately kept distinct from compactness in the derived
category of differential graded modules. -/
@[stacks 09R1 "categorical finite generation of graded modules"]
abbrev IsFinitelyGenerated (P : Graded.{u, v, w} A) : Prop :=
  IsCompactObject P

/-- An external graded right `A`-module is finite projective when it is projective and compact in
the category of graded right `A`-modules.  Equivalently, it is projective and categorically
finitely generated; this compactness is not a derived-category compactness assertion. -/
@[stacks 09R1 "finite projective graded right modules"]
class IsFiniteProjective (P : Graded.{u, v, w} A) : Prop extends
    Projective P, IsCompactObject P

/-- Finite projectivity of a graded module is exactly projectivity together with compactness. -/
theorem isFiniteProjective_iff (P : Graded.{u, v, w} A) :
    IsFiniteProjective A P ↔ Projective P ∧ IsCompactObject P := sorry

/-- The finite-projective condition in its projective plus categorical finite-generation form. -/
@[stacks 09R1 "finite projective as projective and finitely generated"]
theorem isFiniteProjective_iff_projective_finitelyGenerated (P : Graded.{u, v, w} A) :
    IsFiniteProjective A P ↔ Projective P ∧ IsFinitelyGenerated A P := sorry

namespace IsFiniteProjective

section

variable (P : Graded.{u, v, w} A) [IsFiniteProjective A P]

#synth Projective P
#synth IsCompactObject P

end

/-- A finite projective graded module is projective. -/
theorem projective {P : Graded.{u, v, w} A} (hP : IsFiniteProjective A P) :
    Projective P := sorry

/-- A finite projective graded module is compact. -/
theorem isCompactObject {P : Graded.{u, v, w} A} (hP : IsFiniteProjective A P) :
    IsCompactObject P := sorry

end IsFiniteProjective

end Graded

/-- A differential graded right `A`-module is finite graded projective when its external graded
module obtained by forgetting the differential is finite projective. -/
@[stacks 09R1 "finite graded projective differential graded modules"]
abbrev IsFiniteGradedProjective (P : DifferentialGradedModule.{u, v} A) : Prop :=
  Graded.IsFiniteProjective A P.toGraded

section

variable (P : DifferentialGradedModule.{u, v} A) [IsFiniteGradedProjective A P]

#synth Projective P.toGraded
#synth IsCompactObject P.toGraded

end

end DifferentialGradedModule
