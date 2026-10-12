/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_48_3_Normalization
public import stacks_project.Chap66.Lemma_66_10_3_LocalRingDim

/-!
# Codimension-zero points of relative normalizations of algebraic spaces

A codimension-zero point of the relative normalization of a qcqs morphism of algebraic
spaces is the image of a codimension-zero point of the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- Lemma 67.48.7: let `S` be a scheme, and let `f : X ⟶ Y` be a quasi-compact and
quasi-separated morphism of algebraic spaces over `S`. If `x'` is a point of
codimension `0` on the relative normalization `normalization f` of `Y` in `X`,
then `x'` is the image of some point `y` of `X` of codimension `0`.

In Stacks language, `f : Y ⟶ X` and `X'` are Lean `f : X ⟶ Y` and
`Hom.normalization f`, and a point of codimension `0` means `localRingDimAt _ = 0`. -/
@[stacks 0AYG]
theorem exists_map_toNormalization_eq_of_localRingDimAt_eq_zero
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] {x' : Points (normalization f)}
    (hx' : localRingDimAt x' = 0) :
    ∃ y : Points X, localRingDimAt y = 0 ∧ Points.map (toNormalization f) y = x' :=
  sorry

/-- The map on points induced by `toNormalization f` is surjective from the
codimension-`0` points of `X` onto the codimension-`0` points of `normalization f`. -/
theorem surjOn_toNormalization_localRingDimAt_eq_zero
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    Set.SurjOn (Points.map (toNormalization f))
      (setOf fun y : Points X ↦ localRingDimAt y = 0)
      (setOf fun x' : Points (normalization f) ↦ localRingDimAt x' = 0) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
