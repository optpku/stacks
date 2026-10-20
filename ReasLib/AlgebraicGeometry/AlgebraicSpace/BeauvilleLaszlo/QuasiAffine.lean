/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszlo
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiAffine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Quasi-affine Beauville–Laszlo glueing

Glueing triples with quasi-affine components are realized by separated algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing

/-- For a Beauville–Laszlo glueing pair, every object of `Spaces(U ← U' → X')`
whose three components are quasi-affine is isomorphic to the canonical base-change
image of an algebraic space separated over `space R`. -/
@[stacks 0F9U]
theorem exists_separated_of_isQuasiAffine {R R' : Type u} [CommRing R] [CommRing R']
    [Algebra R R'] (f : R) [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f]
    (obj : category R' f) [IsQuasiAffine obj.fst.left]
    [IsQuasiAffine (overlap obj).left] [IsQuasiAffine obj.snd.left] :
    ∃ (Y : Over (space R)), AlgebraicSpace.Separated Y.hom ∧
      Nonempty ((functor R' f).obj Y ≅ obj) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing
