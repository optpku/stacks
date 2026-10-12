/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Subring.SquareCubeOrPrimePower
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism

/-!
# Affine universal homeomorphisms from square-cube-or-prime-power adjunctions

This module characterizes affine universal homeomorphisms in terms of finite successive
square-cube-or-prime-power adjunctions of the corresponding subring.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.UniversalHomeomorphism.SquareCubeOrPrimePower

variable {B : Type u} [CommRing B]

/-- For a subring `A` of `B`, the induced map `Spec(B) ⟶ Spec(A)` is a universal
homeomorphism exactly when finite subsets of `B` are contained in finite successive adjunctions
whose generators satisfy a square-cube or prime-power condition over the preceding subring. -/
theorem specMap_subtype_iff (A : Subring B) :
    UniversalHomeomorphism (Spec.map (CommRingCat.ofHom A.subtype)) ↔
      A.IsFilteredBySquareCubeOrPrimePowerAdjunctions := sorry

end AlgebraicGeometry.UniversalHomeomorphism.SquareCubeOrPrimePower
