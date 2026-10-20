/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy.Whisker
public import ReasLib.Algebra.Homology.DifferentialGradedModule.MappingCone

/-!
# Contractibility of the Mapping Cone of an Identity

The identity cone has its standard explicit contraction.  Keeping its homogeneous coordinate
map visible makes the contraction reusable in DG-module factorizations while retaining
linearity over the full graded algebra.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace DifferentialGradedModule
namespace MappingCone

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}

/-- The second coordinate in the contraction target has the original source degree. -/
theorem contractionTargetIndex (n : ℤ) : n = (n + (-1)) + 1 := sorry

/-- The standard degree-`-1` coordinate `(x, y) ↦ (0, x)` contracting the cone of an identity. -/
def contractionCoordinate (K : DifferentialGradedModule.{u, w} A) (n : ℤ) :
    (mappingCone (𝟙 K)).X n →ₗ[R] (mappingCone (𝟙 K)).X (n + (-1)) :=
  (0 : (mappingCone (𝟙 K)).X n →ₗ[R] K.X (n + (-1))).prod
    (ModuleCat.castLinearMap (congrArg K.X (contractionTargetIndex n))
      (LinearMap.fst R (K.X n) (K.X (n + 1))))

/-- The homogeneous degree-`-1` map underlying the standard contraction of the identity cone. -/
def contractingHom (K : DifferentialGradedModule.{u, w} A) :
    GradedHom A (mappingCone (𝟙 K)) (mappingCone (𝟙 K)) (-1) :=
  ⟨contractionCoordinate K, sorry⟩

/-- The cone of the identity of a DG-module is concretely homotopic to zero. -/
@[stacks 09JW "contraction of the identity mapping cone"]
def homotopyToZero (K : DifferentialGradedModule.{u, w} A) :
    Homotopy (𝟙 (mappingCone (𝟙 K))) 0 where
  hom := contractingHom K
  condition := sorry

end MappingCone
end DifferentialGradedModule
