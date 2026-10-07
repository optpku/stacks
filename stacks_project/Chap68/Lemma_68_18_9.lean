module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_27_6_LocallyQuasiFinite
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap68.Lemma_68_17_4_Relative
public import stacks_project.Chap68.Lemma_68_18_6_Fibre
public import stacks_project.Chap68.Lemma_68_18_10_Fibre

/-!
# Conditions on a point in a fibre and quasi-finiteness

For a locally finite-type morphism of algebraic spaces, the set-theoretic fibre
over a point, a field-valued fibre, and quasi-finiteness at a chosen point of
that fibre are compared by a mixed implication/TFAE diagram. Decency of the
morphism or of the source and target upgrades the one-way arrows.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.18.9 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is locally of finite type. Let `x : Points X`
with image `y = Points.mk p`, and let `xtilde : Points (fieldFiber f p)` map to
`x`. Then the following are equivalent: `{xtilde}` is open in
`Points (fieldFiber f p)`; `xtilde` is closed in `Points (fieldFiber f p)` and
the only specialization into `xtilde` is `xtilde` itself;
`dimensionAt xtilde = 0`; and `f` is quasi-finite at `x`.

These are source conditions (5), (6), (7), and (8). Isolated points are encoded
as open singletons. The field-valued fibre `X_k` is `fieldFiber f p`, and
`|X_k|` is `Points (fieldFiber f p)`. -/
@[stacks 0ACB]
theorem tfae_fieldFiber_isOpen_dimensionAt_quasiFiniteAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (p : FieldValuedPoint Y) (x : Points X) (xtilde : Points (fieldFiber f p))
    (hx : Points.map f x = Points.mk p)
    (hxtilde : Points.map (fieldFiberι f p) xtilde = x) :
    List.TFAE
      [ IsOpen ({xtilde} : Set (Points (fieldFiber f p)))
      , (IsClosed ({xtilde} : Set (Points (fieldFiber f p))) ∧
          (∀ xtilde' : Points (fieldFiber f p),
            Specializes xtilde' xtilde → xtilde' = xtilde))
      , dimensionAt xtilde = (0 : WithBot ℕ∞)
      , QuasiFiniteAt f x ] :=
  sorry

/-- Lemma 68.18.9 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a decent morphism
of algebraic spaces over `S` which is locally of finite type. Let `x : Points X`
with image `y = Points.mk p`, and let `xtilde : Points (fieldFiber f p)` map to
`x`. If `topologicalKrullDimAt xtilde = 0`, then `{xtilde}` is open in
`Points (fieldFiber f p)`.

This is the source arrow (4) ⇒ (5) labeled `f decent`. The hypothesis is
`Decent f`, so the field-valued fibre is a decent algebraic space. -/
@[stacks 0ACB]
theorem isOpen_fieldFiber_of_topologicalKrullDimAt_eq_zero {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] [Decent f]
    (p : FieldValuedPoint Y) (x : Points X) (xtilde : Points (fieldFiber f p))
    (hx : Points.map f x = Points.mk p)
    (hxtilde : Points.map (fieldFiberι f p) xtilde = x)
    (hdim : topologicalKrullDimAt xtilde = (0 : WithBot ℕ∞)) :
    IsOpen ({xtilde} : Set (Points (fieldFiber f p))) :=
  sorry

/-- Lemma 68.18.9 (3): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is locally of finite type, and assume `Y` is
decent. Let `x : Points X` with image `y = Points.mk p`, and let
`xtilde : Points (fieldFiber f p)` map to `x`. Write `F` for the set-theoretic
fibre `fiberOver f (Points.mk p)` with the induced topology. Then the following
are equivalent: `x` is isolated in `F`; `x` is closed in `F` and the only
specialization into `x` in `F` is `x` itself; `{xtilde}` is open in
`Points (fieldFiber f p)`; `xtilde` is closed in `Points (fieldFiber f p)` and
the only specialization into `xtilde` is `xtilde` itself;
`dimensionAt xtilde = 0`; and `f` is quasi-finite at `x`.

These are source conditions (2), (3), (5), (6), (7), and (8). Isolated points
are encoded as open singletons. When `Y` is decent a quasi-compact monomorphism
representative of `Points.mk p` makes `Points.map (fieldFiberι f p)` a
homeomorphism onto `F`. -/
@[stacks 0ACB]
theorem tfae_fiberOver_isOpen_of_isDecent {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDecent Y]
    (p : FieldValuedPoint Y) (x : Points X) (xtilde : Points (fieldFiber f p))
    (hx : Points.map f x = Points.mk p)
    (hxtilde : Points.map (fieldFiberι f p) xtilde = x) :
    List.TFAE
      [ IsOpen ({⟨x, hx⟩} : Set (fiberOver f (Points.mk p)))
      , (IsClosed ({⟨x, hx⟩} : Set (fiberOver f (Points.mk p))) ∧
          (∀ x' : fiberOver f (Points.mk p),
            Specializes x' ⟨x, hx⟩ → x' = ⟨x, hx⟩))
      , IsOpen ({xtilde} : Set (Points (fieldFiber f p)))
      , (IsClosed ({xtilde} : Set (Points (fieldFiber f p))) ∧
          (∀ xtilde' : Points (fieldFiber f p),
            Specializes xtilde' xtilde → xtilde' = xtilde))
      , dimensionAt xtilde = (0 : WithBot ℕ∞)
      , QuasiFiniteAt f x ] :=
  sorry

/-- Lemma 68.18.9 (4): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is locally of finite type, and assume `X` and
`Y` are decent. Let `x : Points X` with image `y = Points.mk p`, and let
`xtilde : Points (fieldFiber f p)` map to `x`. Write `F` for the set-theoretic
fibre `fiberOver f (Points.mk p)` with the induced topology. Then all eight
source conditions are equivalent: `topologicalKrullDimAt` of `x` in `F` is `0`;
`x` is isolated in `F`; `x` is closed in `F` and the only specialization into
`x` in `F` is `x` itself; `topologicalKrullDimAt xtilde = 0`; `{xtilde}` is open
in `Points (fieldFiber f p)`; `xtilde` is closed in `Points (fieldFiber f p)`
and the only specialization into `xtilde` is `xtilde` itself;
`dimensionAt xtilde = 0`; and `f` is quasi-finite at `x`.

These are source conditions (1) through (8) in source order. Isolated points
are encoded as open singletons. -/
@[stacks 0ACB]
theorem tfae_fiberOver_isOpen_of_isDecent_source_target {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDecent X]
    [IsDecent Y] (p : FieldValuedPoint Y) (x : Points X)
    (xtilde : Points (fieldFiber f p)) (hx : Points.map f x = Points.mk p)
    (hxtilde : Points.map (fieldFiberι f p) xtilde = x) :
    List.TFAE
      [ topologicalKrullDimAt (⟨x, hx⟩ : fiberOver f (Points.mk p)) =
          (0 : WithBot ℕ∞)
      , IsOpen ({⟨x, hx⟩} : Set (fiberOver f (Points.mk p)))
      , (IsClosed ({⟨x, hx⟩} : Set (fiberOver f (Points.mk p))) ∧
          (∀ x' : fiberOver f (Points.mk p),
            Specializes x' ⟨x, hx⟩ → x' = ⟨x, hx⟩))
      , topologicalKrullDimAt xtilde = (0 : WithBot ℕ∞)
      , IsOpen ({xtilde} : Set (Points (fieldFiber f p)))
      , (IsClosed ({xtilde} : Set (Points (fieldFiber f p))) ∧
          (∀ xtilde' : Points (fieldFiber f p),
            Specializes xtilde' xtilde → xtilde' = xtilde))
      , dimensionAt xtilde = (0 : WithBot ℕ∞)
      , QuasiFiniteAt f x ] :=
  sorry

/-- For a locally finite-type morphism of algebraic spaces, a point of a
field-valued fibre is isolated if and only if it is closed and has no nontrivial
incoming specialization. -/
theorem isOpen_singleton_fieldFiber_iff_isClosed_specializes {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (p : FieldValuedPoint Y) (x : Points X) (xtilde : Points (fieldFiber f p))
    (hx : Points.map f x = Points.mk p)
    (hxtilde : Points.map (fieldFiberι f p) xtilde = x) :
    IsOpen ({xtilde} : Set (Points (fieldFiber f p))) ↔
      IsClosed ({xtilde} : Set (Points (fieldFiber f p))) ∧
        ∀ xtilde' : Points (fieldFiber f p),
          Specializes xtilde' xtilde → xtilde' = xtilde :=
  sorry

/-- For a locally finite-type morphism of algebraic spaces, a point of a
field-valued fibre is isolated if and only if the étale-local dimension there
vanishes. -/
theorem isOpen_singleton_fieldFiber_iff_dimensionAt_eq_zero {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (p : FieldValuedPoint Y) (x : Points X) (xtilde : Points (fieldFiber f p))
    (hx : Points.map f x = Points.mk p)
    (hxtilde : Points.map (fieldFiberι f p) xtilde = x) :
    IsOpen ({xtilde} : Set (Points (fieldFiber f p))) ↔
      dimensionAt xtilde = (0 : WithBot ℕ∞) :=
  sorry

/-- For a locally finite-type morphism of algebraic spaces, the étale-local
dimension of a field-valued fibre at a lift of `x` vanishes if and only if `f`
is quasi-finite at `x`. -/
theorem dimensionAt_fieldFiber_eq_zero_iff_quasiFiniteAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (p : FieldValuedPoint Y) (x : Points X) (xtilde : Points (fieldFiber f p))
    (hx : Points.map f x = Points.mk p)
    (hxtilde : Points.map (fieldFiberι f p) xtilde = x) :
    dimensionAt xtilde = (0 : WithBot ℕ∞) ↔ QuasiFiniteAt f x :=
  sorry

/-- Quasi-finiteness of the structure morphism of a field-valued fibre at a lift
of `x` is equivalent to quasi-finiteness of `f` at `x`. -/
theorem quasiFiniteAt_fieldFiberToSpec_iff {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (p : FieldValuedPoint Y) (x : Points X) (xtilde : Points (fieldFiber f p))
    (hx : Points.map f x = Points.mk p)
    (hxtilde : Points.map (fieldFiberι f p) xtilde = x) :
    QuasiFiniteAt (fieldFiberToSpec f p) xtilde ↔ QuasiFiniteAt f x :=
  sorry

/-- If `Y` is decent, a point of the set-theoretic fibre is isolated if and only
if it is closed in that fibre and has no nontrivial incoming specialization. -/
theorem isOpen_singleton_fiberOver_iff_isClosed_specializes {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDecent Y]
    (p : FieldValuedPoint Y) (x : Points X) (xtilde : Points (fieldFiber f p))
    (hx : Points.map f x = Points.mk p)
    (hxtilde : Points.map (fieldFiberι f p) xtilde = x) :
    IsOpen ({⟨x, hx⟩} : Set (fiberOver f (Points.mk p))) ↔
      IsClosed ({⟨x, hx⟩} : Set (fiberOver f (Points.mk p))) ∧
        ∀ x' : fiberOver f (Points.mk p),
          Specializes x' ⟨x, hx⟩ → x' = ⟨x, hx⟩ :=
  sorry

/-- If `Y` is decent, a point of the set-theoretic fibre is isolated if and only
if the corresponding point of the field-valued fibre is isolated. -/
theorem isOpen_singleton_fiberOver_iff_isOpen_singleton_fieldFiber
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsDecent Y] (p : FieldValuedPoint Y)
    (x : Points X) (xtilde : Points (fieldFiber f p))
    (hx : Points.map f x = Points.mk p)
    (hxtilde : Points.map (fieldFiberι f p) xtilde = x) :
    IsOpen ({⟨x, hx⟩} : Set (fiberOver f (Points.mk p))) ↔
      IsOpen ({xtilde} : Set (Points (fieldFiber f p))) :=
  sorry

/-- If `X` and `Y` are decent, vanishing of the local topological Krull dimension
of the set-theoretic fibre at `x` is equivalent to quasi-finiteness of `f` at
`x`. -/
theorem topologicalKrullDimAt_fiberOver_eq_zero_iff_quasiFiniteAt
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsDecent X] [IsDecent Y]
    (p : FieldValuedPoint Y) (x : Points X) (xtilde : Points (fieldFiber f p))
    (hx : Points.map f x = Points.mk p)
    (hxtilde : Points.map (fieldFiberι f p) xtilde = x) :
    topologicalKrullDimAt (⟨x, hx⟩ : fiberOver f (Points.mk p)) =
        (0 : WithBot ℕ∞) ↔
      QuasiFiniteAt f x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
