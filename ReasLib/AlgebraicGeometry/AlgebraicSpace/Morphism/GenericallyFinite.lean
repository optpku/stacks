/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.LocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.CodimensionZero
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.Locality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber.QuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions.Implications
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions.InheritedFromTarget

/-!
# Generically finite morphisms of algebraic spaces

For a quasi-separated finite-type morphism of algebraic spaces, finiteness of a
field-valued fibre over a codimension-zero point is equivalent to pointwise
quasi-finiteness over that point and to finiteness of the morphism after
shrinking the target to an open subspace. If the target is decent, these are
also equivalent to finiteness of the set-theoretic fibre.

A locally finite type morphism to a decent target with finite codimension-zero
point sets satisfying `f⁻¹(Y⁰) = X⁰` is finite over a dense open of the target
if it is quasi-compact or separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
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

/-- Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
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
      , (fiberOver f (Points.mk p)).Finite ] := by
  haveI : IsDecent X := IsDecent.of_decent f
  have hfinite : (fiberOver f (Points.mk p)).Finite ↔
      Finite (Points (fieldFiber f p)) := by
    constructor
    · intro h
      letI := h.to_subtype
      exact finite_fieldFiber_of_isDecent_finite f p
    · exact finite_fiberOver_of_finite_fieldFiber f p
  have h := tfae_finite_fieldFiber_quasiFiniteAt_isFinite_open f p hy
  apply List.tfae_of_forall (Finite (Points (fieldFiber f p)))
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact Iff.rfl
  · exact h.out 1 0
  · exact h.out 2 0
  · exact hfinite

/-- Finiteness of the points of a field-valued fibre over a codimension-zero
point is equivalent to quasi-finiteness at every point of the source over that
point. -/
theorem finite_fieldFiber_iff_quasiFiniteAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f] [FiniteType f]
    (p : FieldValuedPoint Y) (hy : localRingDimAt (Points.mk p) = 0) :
    Finite (Points (fieldFiber f p)) ↔
      ∀ x : Points X, Points.map f x = Points.mk p → QuasiFiniteAt f x :=
  (tfae_finite_fieldFiber_quasiFiniteAt_isFinite_open f p hy).out 0 1

/-- Quasi-finiteness at every point over a codimension-zero point is equivalent
to the existence of an open subspace of the target containing that point on
which the base change is finite. -/
theorem quasiFiniteAt_iff_exists_isFinite_open {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f] [FiniteType f]
    (p : FieldValuedPoint Y) (hy : localRingDimAt (Points.mk p) = 0) :
    (∀ x : Points X, Points.map f x = Points.mk p → QuasiFiniteAt f x) ↔
      ∃ Y' : OpenSubspace Y,
        Points.mk p ∈ Y'.pointsSet ∧ IsFinite (pullback.snd f Y'.ι) :=
  (tfae_finite_fieldFiber_quasiFiniteAt_isFinite_open f p hy).out 1 2

/-- Finiteness of the points of a field-valued fibre over a codimension-zero
point is equivalent to the existence of an open subspace of the target
containing that point on which the base change is finite. -/
theorem finite_fieldFiber_iff_exists_isFinite_open {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f] [FiniteType f]
    (p : FieldValuedPoint Y) (hy : localRingDimAt (Points.mk p) = 0) :
    Finite (Points (fieldFiber f p)) ↔
      ∃ Y' : OpenSubspace Y,
        Points.mk p ∈ Y'.pointsSet ∧ IsFinite (pullback.snd f Y'.ι) :=
  (tfae_finite_fieldFiber_quasiFiniteAt_isFinite_open f p hy).out 0 2

/-- If the target is decent, finiteness of the set-theoretic fibre over a
codimension-zero point is equivalent to finiteness of the points of a
field-valued fibre representing that point. -/
theorem finite_fiberOver_iff_finite_fieldFiber_of_isDecent {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f] [FiniteType f]
    [IsDecent Y] (p : FieldValuedPoint Y)
    (hy : localRingDimAt (Points.mk p) = 0) :
    (fiberOver f (Points.mk p)).Finite ↔ Finite (Points (fieldFiber f p)) :=
  (tfae_finite_fieldFiber_quasiFiniteAt_isFinite_open_of_isDecent f p hy).out 3 0

/-- Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume that `f` is quasi-separated and locally of
finite type and `Y` quasi-separated. Let `y ∈ |Y|` be a point of
codimension `0` on `Y`. The following are equivalent: the set `f⁻¹({y})` is
finite; the space `|X_k|` is finite where `Spec(k) ⟶ Y` represents `y`;
there exist open subspaces `X' ⊂ X` and `Y' ⊂ Y` with `f(X') ⊂ Y'`,
`y ∈ |Y'|`, and `f⁻¹({y}) ⊂ |X'|` such that the restriction `X' ⟶ Y'` is
finite.

Here `y` is `Points.mk p` for a field-valued representative `p` with `p.hom`
playing the role of `Spec(k) ⟶ Y`, `|X_k|` is `Points (fieldFiber f p)`,
`f⁻¹({y})` is `fiberOver f (Points.mk p)`, a point of codimension `0` means
`localRingDimAt (Points.mk p) = 0`, `|Y'|` and `|X'|` are `Y'.pointsSet`
and `X'.pointsSet`, and the restriction `X' ⟶ Y'` is a morphism
`g : X'.X ⟶ Y'.X` satisfying `g ≫ Y'.ι = X'.ι ≫ f`. -/
@[stacks 0AD0]
theorem tfae_finite_fiberOver_fieldFiber_exists_isFinite_restrict {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f] [LocallyOfFiniteType f]
    [IsAbsolutelyQuasiSeparated Y] (p : FieldValuedPoint Y)
    (hy : localRingDimAt (Points.mk p) = 0) :
    List.TFAE
      [ (fiberOver f (Points.mk p)).Finite
      , Finite (Points (fieldFiber f p))
      , ∃ (X' : OpenSubspace X) (Y' : OpenSubspace Y) (g : X'.X ⟶ Y'.X),
          g ≫ Y'.ι = X'.ι ≫ f ∧ Points.mk p ∈ Y'.pointsSet ∧
            fiberOver f (Points.mk p) ⊆ X'.pointsSet ∧ IsFinite g ] :=
  sorry

/-- Finiteness of the set-theoretic fibre over a codimension-zero point is
equivalent to finiteness of the points of a field-valued fibre representing
that point. -/
theorem finite_fiberOver_iff_finite_fieldFiber {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f] [LocallyOfFiniteType f]
    [IsAbsolutelyQuasiSeparated Y] (p : FieldValuedPoint Y)
    (hy : localRingDimAt (Points.mk p) = 0) :
    (fiberOver f (Points.mk p)).Finite ↔ Finite (Points (fieldFiber f p)) :=
  (tfae_finite_fiberOver_fieldFiber_exists_isFinite_restrict f p hy).out 0 1

/-- Finiteness of the points of a field-valued fibre over a codimension-zero
point is equivalent to the existence of open subspaces of the source and
target, containing the fibre and the point, on which `f` restricts to a finite
morphism. -/
theorem finite_fieldFiber_iff_exists_isFinite_restrict {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f] [LocallyOfFiniteType f]
    [IsAbsolutelyQuasiSeparated Y] (p : FieldValuedPoint Y)
    (hy : localRingDimAt (Points.mk p) = 0) :
    Finite (Points (fieldFiber f p)) ↔
      ∃ (X' : OpenSubspace X) (Y' : OpenSubspace Y) (g : X'.X ⟶ Y'.X),
        g ≫ Y'.ι = X'.ι ≫ f ∧ Points.mk p ∈ Y'.pointsSet ∧
          fiberOver f (Points.mk p) ⊆ X'.pointsSet ∧ IsFinite g :=
  (tfae_finite_fiberOver_fieldFiber_exists_isFinite_restrict f p hy).out 1 2

/-- Finiteness of the set-theoretic fibre over a codimension-zero point is
equivalent to the existence of open subspaces of the source and target,
containing the fibre and the point, on which `f` restricts to a finite
morphism. -/
theorem finite_fiberOver_iff_exists_isFinite_restrict {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiSeparated f] [LocallyOfFiniteType f]
    [IsAbsolutelyQuasiSeparated Y] (p : FieldValuedPoint Y)
    (hy : localRingDimAt (Points.mk p) = 0) :
    (fiberOver f (Points.mk p)).Finite ↔
      ∃ (X' : OpenSubspace X) (Y' : OpenSubspace Y) (g : X'.X ⟶ Y'.X),
        g ≫ Y'.ι = X'.ι ≫ f ∧ Points.mk p ∈ Y'.pointsSet ∧
          fiberOver f (Points.mk p) ⊆ X'.pointsSet ∧ IsFinite g :=
  (tfae_finite_fiberOver_fieldFiber_exists_isFinite_restrict f p hy).out 0 2

/-- A locally finite type morphism of algebraic spaces to a decent target,
with finite codimension-zero point sets satisfying `f⁻¹(Y⁰) = X⁰`, is finite
over a dense open of the target if it is quasi-compact or separated. -/
@[stacks 0BBC]
theorem exists_dense_open_isFinite_restrict_of_preimage_codimZeroPoints_eq
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsDecent Y]
    (hX : (codimZeroPoints X).Finite) (hY : (codimZeroPoints Y).Finite)
    (hpreimage : Points.map f ⁻¹' codimZeroPoints Y = codimZeroPoints X)
    (hqc_or_sep : QuasiCompact f ∨ Separated f) :
    ∃ V : OpenSubspace Y, Dense V.pointsSet ∧ IsFinite (pullback.snd f V.ι) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
