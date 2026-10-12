/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.List.TFAE
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_10_3_LocalRingDim
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_27_6_LocallyQuasiFinite
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap68.Lemma_68_18_6_Fibre
public import stacks_project.Chap68.Lemma_68_18_10_Fibre

/-!
# Generically finite morphisms of algebraic spaces

For a quasi-separated finite-type morphism of algebraic spaces, finiteness of a
field-valued fibre over a codimension-zero point is equivalent to pointwise
quasi-finiteness over that point and to finiteness of the morphism after
shrinking the target to an open subspace. If the target is decent, these are
also equivalent to finiteness of the set-theoretic fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.21.1 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume that `f` is quasi-separated of finite type.
Let `y ∈ |Y|` be a point of codimension `0` on `Y`. The following are
equivalent: the space `|X_k|` is finite where `Spec(k) ⟶ Y` represents `y`;
`f` is quasi-finite at all points of `|X|` over `y`; there exists an open
subspace `Y' ⊂ Y` with `y ∈ |Y'|` such that `Y' ×_Y X ⟶ Y'` is finite.

Here `y` is `Points.mk p` for a field-valued representative `p` with
`p.hom` playing the role of `Spec(k) ⟶ Y`, `|X_k|` is
`Points (fieldFiber f p)`, a point of codimension `0` means
`localRingDimAt (Points.mk p) = 0`, quasi-finiteness at a point is
`QuasiFiniteAt`, `|Y'|` is `Y'.pointsSet`, and `Y' ×_Y X ⟶ Y'` is
`pullback.snd f Y'.ι`. -/
@[stacks 0ACZ]
theorem tfae_finite_fieldFiber_quasiFiniteAt_isFinite_open {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f] [FiniteType f]
    (p : FieldValuedPoint Y) (hy : localRingDimAt (Points.mk p) = 0) :
    List.TFAE
      [ Finite (Points (fieldFiber f p))
      , ∀ x : Points X, Points.map f x = Points.mk p → QuasiFiniteAt f x
      , ∃ Y' : OpenSubspace Y,
          Points.mk p ∈ Y'.pointsSet ∧ IsFinite (pullback.snd f Y'.ι) ] :=
  sorry

/-- Lemma 68.21.1 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume that `f` is quasi-separated of finite type
and that `Y` is decent. Let `y ∈ |Y|` be a point of codimension `0` on `Y`.
The following are equivalent: the space `|X_k|` is finite where `Spec(k) ⟶ Y`
represents `y`; `f` is quasi-finite at all points of `|X|` over `y`; there
exists an open subspace `Y' ⊂ Y` with `y ∈ |Y'|` such that `Y' ×_Y X ⟶ Y'`
is finite; the set `f⁻¹({y})` is finite.

Here `y` is `Points.mk p`, `|X_k|` is `Points (fieldFiber f p)`,
`Y' ×_Y X ⟶ Y'` is `pullback.snd f Y'.ι`, and `f⁻¹({y})` is
`fiberOver f (Points.mk p)`. -/
@[stacks 0ACZ]
theorem tfae_finite_fieldFiber_quasiFiniteAt_isFinite_open_of_isDecent
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f]
    [FiniteType f] [IsDecent Y] (p : FieldValuedPoint Y)
    (hy : localRingDimAt (Points.mk p) = 0) :
    List.TFAE
      [ Finite (Points (fieldFiber f p))
      , ∀ x : Points X, Points.map f x = Points.mk p → QuasiFiniteAt f x
      , ∃ Y' : OpenSubspace Y,
          Points.mk p ∈ Y'.pointsSet ∧ IsFinite (pullback.snd f Y'.ι)
      , (fiberOver f (Points.mk p)).Finite ] :=
  sorry

/-- Finiteness of the points of a field-valued fibre over a codimension-zero
point is equivalent to quasi-finiteness at every point of the source over that
point. -/
theorem finite_fieldFiber_iff_quasiFiniteAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f] [FiniteType f]
    (p : FieldValuedPoint Y) (hy : localRingDimAt (Points.mk p) = 0) :
    Finite (Points (fieldFiber f p)) ↔
      ∀ x : Points X, Points.map f x = Points.mk p → QuasiFiniteAt f x :=
  sorry

/-- Quasi-finiteness at every point over a codimension-zero point is equivalent
to the existence of an open subspace of the target containing that point on
which the base change is finite. -/
theorem quasiFiniteAt_iff_exists_isFinite_open {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f] [FiniteType f]
    (p : FieldValuedPoint Y) (hy : localRingDimAt (Points.mk p) = 0) :
    (∀ x : Points X, Points.map f x = Points.mk p → QuasiFiniteAt f x) ↔
      ∃ Y' : OpenSubspace Y,
        Points.mk p ∈ Y'.pointsSet ∧ IsFinite (pullback.snd f Y'.ι) :=
  sorry

/-- Finiteness of the points of a field-valued fibre over a codimension-zero
point is equivalent to the existence of an open subspace of the target
containing that point on which the base change is finite. -/
theorem finite_fieldFiber_iff_exists_isFinite_open {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f] [FiniteType f]
    (p : FieldValuedPoint Y) (hy : localRingDimAt (Points.mk p) = 0) :
    Finite (Points (fieldFiber f p)) ↔
      ∃ Y' : OpenSubspace Y,
        Points.mk p ∈ Y'.pointsSet ∧ IsFinite (pullback.snd f Y'.ι) :=
  sorry

/-- If the target is decent, finiteness of the set-theoretic fibre over a
codimension-zero point is equivalent to finiteness of the points of a
field-valued fibre representing that point. -/
theorem finite_fiberOver_iff_finite_fieldFiber_of_isDecent {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f] [FiniteType f]
    [IsDecent Y] (p : FieldValuedPoint Y)
    (hy : localRingDimAt (Points.mk p) = 0) :
    (fiberOver f (Points.mk p)).Finite ↔ Finite (Points (fieldFiber f p)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
