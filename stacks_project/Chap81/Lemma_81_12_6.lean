/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszlo.QuasiAffine
import StacksCheckRecall

/-!
# Lemma 81.12.6

For a Beauville–Laszlo glueing pair, every object of
`Spaces(U ← U' → X')` with quasi-affine components is isomorphic to the
image under `functor R' f` of a separated algebraic space over `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing

noncomputable section

universe u

/- Lemma 81.12.6: let `(algebraMap R R', f)` be a glueing pair. Any object
`obj` of `category R' f`, that is of `Spaces(U ← U' → X')`, whose components
`V = obj.fst.left`, `V' = (overlap obj).left`, and `Y' = obj.snd.left` are
quasi-affine is isomorphic to the image under `functor R' f` (81.12.0.1) of a
separated algebraic space `Y` over `X = space R`. -/
@[stacks 0F9U] #check
  (AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing.exists_separated_of_isQuasiAffine :
    ∀ {R R' : Type u} [CommRing R] [CommRing R']
    [Algebra R R'] (f : R) [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f]
    (obj : category R' f) [IsQuasiAffine obj.fst.left]
    [IsQuasiAffine (overlap obj).left] [IsQuasiAffine obj.snd.left],
    ∃ (Y : Over (space R)), AlgebraicSpace.Separated Y.hom ∧
      Nonempty ((functor R' f).obj Y ≅ obj))
