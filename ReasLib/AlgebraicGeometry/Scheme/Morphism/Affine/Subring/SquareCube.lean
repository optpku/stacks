/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Subring.SquareCube
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Subring
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Subalgebra
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.FilteredColimit

/-!
# Affine universal homeomorphisms from square-cube adjunctions

This module characterizes affine universal homeomorphisms inducing residue-field isomorphisms in
terms of finite successive square-cube adjunctions of the corresponding subring.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.UniversalHomeomorphism.SquareCube

variable {B : Type u} [CommRing B]

/-- For a subring `A` of `B`, the induced map `Spec(B) ⟶ Spec(A)` is a universal
homeomorphism inducing isomorphisms on residue fields exactly when finite subsets of `B` are
contained in finite successive square-cube adjunctions over `A`. -/
theorem specMap_subtype_iff (A : Subring B) :
    (UniversalHomeomorphism (Spec.map (CommRingCat.ofHom A.subtype)) ∧
      ∀ x : Spec (CommRingCat.of B),
        IsIso ((Spec.map (CommRingCat.ofHom A.subtype)).residueFieldMap x)) ↔
      A.IsFilteredBySquareCubeAdjunctions := sorry

end AlgebraicGeometry.UniversalHomeomorphism.SquareCube
