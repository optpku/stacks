/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.PropertyP
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.Resolution

/-!
# Property P Resolutions of Differential Graded Bimodules
-/

@[expose] public section

universe u v w

namespace DifferentialGradedBimodule.PropertyP

variable {R : Type u} [CommRing R]

section EnvelopingCarrier

variable (A : CochainDGAlgebra.{u, v} R) (B : CochainDGAlgebra.{u, w} R)

/-- A property P resolution of a DG `(A, B)`-bimodule is a specified quasi-isomorphism from a
specified property P module over `A.opposite ⊗[R] B`. -/
@[stacks 0FQK "property-P resolutions of differential graded bimodules"]
abbrev Resolution (M : DifferentialGradedBimodule.{u, max v w, v, w} A B) :=
  DifferentialGradedModule.PropertyP.Resolution
    (CochainDGAlgebra.enveloping A B) M

namespace Resolution

/-- The resolving bimodule in a bimodule Property-P resolution has the enveloping Property P. -/
@[stacks 0FQK "property P of a bimodule resolution object"]
theorem propertyP_obj
    {M : DifferentialGradedBimodule.{u, max v w, v, w} A B}
    (P : Resolution A B M) :
    DifferentialGradedBimodule.HasPropertyP A B P.obj := sorry

/-- Every DG `(A, B)`-bimodule admits a bimodule Property-P resolution. -/
@[stacks 0FQK "existence of bimodule property-P resolutions"]
theorem nonempty
    (M : DifferentialGradedBimodule.{u, max v w, v, w} A B) :
    Nonempty (Resolution A B M) := sorry

end Resolution

variable (M : DifferentialGradedBimodule.{u, max v w, v, w} A B)

/- Lemma 22.28.4 (0FQK): every DG `(A, B)`-bimodule admits a property P resolution. -/

end EnvelopingCarrier

end DifferentialGradedBimodule.PropertyP
