/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Ring.Subring.EqLocus
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Operations
public import ReasLib.LinearAlgebra.Determinant.Projective
public import ReasLib.RingTheory.Flatness.LocallyFree.Finite

/-!
# Norms for affine groupoid schemes

This module records the invariance of the finite-projective norm for affine presentations of
groupoid schemes.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- For an affine presentation of a groupoid scheme whose source and target are finite locally
free, the finite-projective norm along the source of the target pullback of an object-ring element
belongs to the equalizer subring of invariant elements. -/
theorem norm_target_mem_eqLocus {S : Scheme.{u}} (G : GroupoidScheme S)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FiniteLocallyFree A B] (tSharp : A →+* B)
    (eU : Spec (CommRingCat.of A) ≅ G.U.left) (eR : Spec (CommRingCat.of B) ≅ G.R.left)
    (h_source : eR.hom ≫ G.s.left =
      Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
    (h_target : eR.hom ≫ G.t.left = Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
    [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left] (f : A) :
    LinearMap.projectiveDet (Algebra.lmul A B (tSharp f)) ∈
      tSharp.eqLocus (algebraMap A B) := sorry

end AlgebraicGeometry.GroupoidScheme
