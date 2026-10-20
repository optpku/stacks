/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Affine
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# Subcanonicality of pro-étale sites

The small affine pro-étale topology and the topologies of a chosen big
pro-étale presentation are subcanonical.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.ProEt

/-- The small affine pro-étale topology of a scheme is subcanonical. -/
@[stacks 098Z]
instance affineTopology_subcanonical (S : Scheme.{u}) :
    (affineTopology S).Subcanonical := sorry

end AlgebraicGeometry.Scheme.ProEt

namespace AlgebraicGeometry.ChosenBigProetaleSite

/-- The chosen big affine pro-étale topology of a scheme is subcanonical. -/
@[stacks 098Z]
theorem bigAffineTopology_subcanonical (X : ChosenBigProetaleSite.{u, v})
    (S : X.carrier) : (bigAffineTopology X S).Subcanonical := sorry

/-- The topology of a chosen big pro-étale presentation is subcanonical. -/
theorem toGrothendieck_subcanonical (X : ChosenBigProetaleSite.{u, v}) :
    X.toGrothendieck.Subcanonical := sorry

/-- The chosen big pro-étale slice topology of a scheme is subcanonical. -/
theorem bigTopology_subcanonical (X : ChosenBigProetaleSite.{u, v})
    (S : X.carrier) : (bigTopology X S).Subcanonical := sorry

/-- The chosen small pro-étale topology of a scheme is subcanonical. -/
theorem smallTopology_subcanonical (X : ChosenBigProetaleSite.{u, v})
    (S : X.carrier) : (smallTopology X S).Subcanonical := sorry

/-- The big, small, slice, small affine, and big affine pro-étale topologies
associated to a chosen presentation and a represented base scheme are subcanonical. -/
theorem topologies_subcanonical (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier) :
    X.toGrothendieck.Subcanonical ∧
      (smallTopology X S).Subcanonical ∧
      (bigTopology X S).Subcanonical ∧
      (AlgebraicGeometry.Scheme.ProEt.affineTopology (X.toScheme.obj S)).Subcanonical ∧
      (bigAffineTopology X S).Subcanonical :=
  ⟨toGrothendieck_subcanonical X, smallTopology_subcanonical X S,
    bigTopology_subcanonical X S,
    AlgebraicGeometry.Scheme.ProEt.affineTopology_subcanonical (X.toScheme.obj S),
    bigAffineTopology_subcanonical X S⟩

end AlgebraicGeometry.ChosenBigProetaleSite
