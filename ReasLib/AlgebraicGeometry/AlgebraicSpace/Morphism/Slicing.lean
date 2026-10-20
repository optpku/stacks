/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Regular.RegularSequence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.Germ
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Vanishing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support

/-! # Slicing flat locally finitely presented morphisms of algebraic spaces -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S` which is flat and locally of finite presentation, and let `p` be a
field-valued point of `Y`. Let `fs` be a finite family of global sections of `𝒪_X`
and let `z` be a point of the fibre `F = X ×_Y Spec(k)` with geometric point `zbar`
lying over `z`, such that the images of `fs` form a regular sequence in
`𝒪_{F, zbar}`. Then after replacing `X` by an open subspace containing the image of
`z` in `|X|`, the morphism `V(fs) ⟶ Y` is flat and locally of finite presentation. -/
@[stacks 06LW]
theorem exists_openSubspace_vanishingSubspace_flat_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] (p : FieldValuedPoint Y) {r : ℕ}
    (fs : Fin r → globalSectionsRing X) (z : Points (fieldFiber f p))
    (zbar : GeometricPoint (fieldFiber f p)) (hz : zbar.liesOver z)
    (hreg : ∀ (U : smallEtaleSite X)
        (l : (toSmallEtalePoint (zbar.map (fieldFiberι f p))).fiber.obj U),
      RingTheory.Sequence.IsRegular (etaleLocalRing (fieldFiber f p) zbar)
        (List.ofFn fun i ↦
          globalSectionsToFiberEtaleLocalRingAt f p zbar U l (fs i))) :
    ∃ U : OpenSubspace X,
      Points.map (fieldFiberι f p) z ∈ U.pointsSet ∧
        Flat (vanishingPullbackHom f fs U) ∧
          LocallyOfFinitePresentation (vanishingPullbackHom f fs U) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
