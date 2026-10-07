module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo
public import stacks_project.Chap67.Definition_67_21_2_QuasiAffine
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap81.«81_12_0_1_Glueing»

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

namespace AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing

/-- Lemma 81.12.6: let `(algebraMap R R', f)` be a glueing pair. Any object
`obj` of `category R' f`, that is of `Spaces(U ← U' → X')`, whose components
`V = obj.fst.left`, `V' = (overlap obj).left`, and `Y' = obj.snd.left` are
quasi-affine is isomorphic to the image under `functor R' f` (81.12.0.1) of a
separated algebraic space `Y` over `X = space R`. -/
@[stacks 0F9U]
theorem exists_separated_of_isQuasiAffine {R R' : Type u} [CommRing R] [CommRing R']
    [Algebra R R'] (f : R) [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f]
    (obj : category R' f) [IsQuasiAffine obj.fst.left]
    [IsQuasiAffine (overlap obj).left] [IsQuasiAffine obj.snd.left] :
    ∃ (Y : Over (space R)), AlgebraicSpace.Separated Y.hom ∧
      Nonempty ((functor R' f).obj Y ≅ obj) :=
  sorry

/-- An object of `category R' f` with quasi-affine components `obj.fst.left`,
`(overlap obj).left`, and `obj.snd.left` is isomorphic to the image under
`functor R' f` of some separated algebraic space over `space R`. -/
theorem exists_separated_of_isQuasiAffine_of {R R' : Type u} [CommRing R] [CommRing R']
    [Algebra R R'] (f : R) [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f]
    (obj : category R' f) (h_fst : IsQuasiAffine obj.fst.left)
    (h_overlap : IsQuasiAffine (overlap obj).left)
    (h_snd : IsQuasiAffine obj.snd.left) :
    ∃ (Y : Over (space R)), AlgebraicSpace.Separated Y.hom ∧
      Nonempty ((functor R' f).obj Y ≅ obj) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing
