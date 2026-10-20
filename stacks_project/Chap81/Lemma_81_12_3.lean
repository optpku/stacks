/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszlo.AffineMorphismProperties
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing

universe u

/- Lemma 81.12.3
For a Beauville–Laszlo glueing pair, the canonical equivalence on affine glueable
algebraic spaces identifies the six morphism properties with the same properties
on all three components of the corresponding affine triples.
-/
@[stacks 0F9R] #check
  (AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing.functor_map_property_iff :
    ∀ {R R' : Type u} [CommRing R] [CommRing R']
    [Algebra R R'] (f : R) [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f]
    (P : AffineMorphismKind) {Y Z : Over (space R)}
    (hY : affineGlueableProperty R' f Y) (hZ : affineGlueableProperty R' f Z)
    (α : Y ⟶ Z),
    P.property α.left ↔
      P.property ((functor R' f).map α).fst.left ∧
        P.property (overlapMap ((functor R' f).map α)).left ∧
        P.property ((functor R' f).map α).snd.left)
