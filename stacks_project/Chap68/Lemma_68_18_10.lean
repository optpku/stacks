module

public import Mathlib.Data.Finite.Defs
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
# Conditions on fibres and quasi-finiteness

For a locally finite-type morphism of algebraic spaces, the set-theoretic fibre
over a point, the field-valued fibre, and pointwise quasi-finiteness over that
point are compared by a mixed implication/TFAE diagram. Decency of the morphism
or of the source and target upgrades the one-way arrows.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.18.10 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is locally of finite type. Let `p` be a
field-valued point of `Y`. Then the following are equivalent:
`Points (fieldFiber f p)` is discrete,
`topologicalKrullDim (Points (fieldFiber f p)) ≤ 0`,
`dimension (fieldFiber f p) ≤ 0`, and `f` is quasi-finite at every point of
`Points X` lying over `Points.mk p`.

These are source conditions (5), (6), (7), and (8). The source writes
`dim(|X_k|) = 0` and `dim(X_k) = 0`; the Lean statements use `≤ 0` so that the
empty fibre, whose dimensions are `⊥`, is included. -/
@[stacks 0ACK]
theorem tfae_fieldFiber_discrete_dimension_quasiFiniteAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (p : FieldValuedPoint Y) :
    List.TFAE
      [ DiscreteTopology (Points (fieldFiber f p))
      , topologicalKrullDim (Points (fieldFiber f p)) ≤ 0
      , dimension (fieldFiber f p) ≤ 0
      , ∀ x : Points X, Points.map f x = Points.mk p → QuasiFiniteAt f x ] :=
  sorry

/-- Lemma 68.18.10 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is locally of finite type. Let `p` be a
field-valued point of `Y`. If `Points (fieldFiber f p)` is finite, then the
set-theoretic fibre `fiberOver f (Points.mk p)` is finite.

This is the unconditional source arrow (4) ⇒ (1), from surjectivity of
`Points.map (fieldFiberι f p)` onto the set-theoretic fibre. -/
@[stacks 0ACK]
theorem finite_fiberOver_of_finite_fieldFiber {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (p : FieldValuedPoint Y) (hXk : Finite (Points (fieldFiber f p))) :
    (fiberOver f (Points.mk p)).Finite :=
  sorry

/-- Lemma 68.18.10 (3): Let `S` be a scheme. Let `f : X ⟶ Y` be a decent morphism
of algebraic spaces over `S` which is locally of finite type. Let `p` be a
field-valued point of `Y`. If `Points (fieldFiber f p)` is finite, then
`Points (fieldFiber f p)` is discrete.

This is the source arrow (4) ⇒ (5) labeled `f decent`. The hypothesis is
`Decent f`, so the field-valued fibre is a decent algebraic space. -/
@[stacks 0ACK]
theorem discreteTopology_fieldFiber_of_decent_finite {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] [Decent f]
    (p : FieldValuedPoint Y) (hXk : Finite (Points (fieldFiber f p))) :
    DiscreteTopology (Points (fieldFiber f p)) :=
  sorry

/-- Lemma 68.18.10 (4): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is locally of finite type, and assume `Y` is
decent. Let `p` be a field-valued point of `Y`. Then the following are
equivalent: `fiberOver f (Points.mk p)` is discrete,
`topologicalKrullDim (fiberOver f (Points.mk p)) ≤ 0`,
`Points (fieldFiber f p)` is discrete,
`topologicalKrullDim (Points (fieldFiber f p)) ≤ 0`,
`dimension (fieldFiber f p) ≤ 0`, and `f` is quasi-finite at every point of
`Points X` lying over `Points.mk p`.

These are source conditions (2), (3), (5), (6), (7), and (8). The source writes
`dim(F) = 0`, `dim(|X_k|) = 0`, and `dim(X_k) = 0`; the Lean statements use
`≤ 0` so that the empty fibre, whose dimensions are `⊥`, is included. When `Y`
is decent a quasi-compact monomorphism representative of `Points.mk p` makes
`Points.map (fieldFiberι f p)` a homeomorphism onto the set-theoretic fibre. -/
@[stacks 0ACK]
theorem tfae_fiberOver_of_isDecent {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDecent Y] (p : FieldValuedPoint Y) :
    List.TFAE
      [ DiscreteTopology (fiberOver f (Points.mk p))
      , topologicalKrullDim (fiberOver f (Points.mk p)) ≤ 0
      , DiscreteTopology (Points (fieldFiber f p))
      , topologicalKrullDim (Points (fieldFiber f p)) ≤ 0
      , dimension (fieldFiber f p) ≤ 0
      , ∀ x : Points X, Points.map f x = Points.mk p → QuasiFiniteAt f x ] :=
  sorry

/-- Lemma 68.18.10 (5): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is locally of finite type, and assume `X` and
`Y` are decent. Let `p` be a field-valued point of `Y`. If the set-theoretic
fibre `fiberOver f (Points.mk p)` is finite, then `f` is quasi-finite at every
point of `Points X` lying over `Points.mk p`.

This is the source implication (1) ⇒ (8). Conditions (2), (3), and (5)–(8)
then follow from this implication together with the TFAEs in (1) and (4).
The remaining non-equivalent clause (1) ⇒ (4) of the last sentence is (6). -/
@[stacks 0ACK]
theorem quasiFiniteAt_fiberOver_of_isDecent_finite {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDecent X]
    [IsDecent Y] (p : FieldValuedPoint Y)
    (hF : (fiberOver f (Points.mk p)).Finite) :
    ∀ x : Points X, Points.map f x = Points.mk p → QuasiFiniteAt f x :=
  sorry

/-- Lemma 68.18.10 (6): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is locally of finite type, and assume `X` and
`Y` are decent. Let `p` be a field-valued point of `Y`. If the set-theoretic
fibre `fiberOver f (Points.mk p)` is finite, then `Points (fieldFiber f p)` is
finite.

This is the source implication (1) ⇒ (4) from the last sentence. Quasi-finiteness
does not imply finiteness of the field-valued fibre, so this clause is not
recovered from (5) or the TFAEs. The given representative `p` need not be a
quasi-compact monomorphism, so this is not claimed as a homeomorphism. -/
@[stacks 0ACK]
theorem finite_fieldFiber_of_isDecent_finite {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDecent X]
    [IsDecent Y] (p : FieldValuedPoint Y)
    (hF : (fiberOver f (Points.mk p)).Finite) :
    Finite (Points (fieldFiber f p)) :=
  sorry

/-- For a locally finite-type morphism of algebraic spaces, discreteness of the
points of a field-valued fibre is equivalent to vanishing of their topological
Krull dimension. The source writes equality with `0`; `≤ 0` includes the empty
fibre, whose dimension is `⊥`. -/
theorem discreteTopology_fieldFiber_iff_topologicalKrullDim_le_zero
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (p : FieldValuedPoint Y) :
    DiscreteTopology (Points (fieldFiber f p)) ↔
      topologicalKrullDim (Points (fieldFiber f p)) ≤ 0 :=
  sorry

/-- For a locally finite-type morphism of algebraic spaces, vanishing of the
topological Krull dimension of the points of a field-valued fibre is equivalent
to vanishing of the étale-local dimension of that fibre. The source writes
equality with `0`; `≤ 0` includes the empty fibre, whose dimension is `⊥`. -/
theorem topologicalKrullDim_fieldFiber_le_zero_iff_dimension_le_zero
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (p : FieldValuedPoint Y) :
    topologicalKrullDim (Points (fieldFiber f p)) ≤ 0 ↔
      dimension (fieldFiber f p) ≤ 0 :=
  sorry

/-- For a locally finite-type morphism of algebraic spaces, vanishing of the
étale-local dimension of a field-valued fibre is equivalent to quasi-finiteness
of `f` at every point of `Points X` lying over the class of `p`. The source
writes equality with `0`; `≤ 0` includes the empty fibre, whose dimension is
`⊥`. -/
theorem dimension_fieldFiber_le_zero_iff_quasiFiniteAt_fiberOver
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (p : FieldValuedPoint Y) :
    dimension (fieldFiber f p) ≤ 0 ↔
      ∀ x : Points X, Points.map f x = Points.mk p → QuasiFiniteAt f x :=
  sorry

/-- Quasi-finiteness of `f` at every point over the class of `p` is membership
of every point of the set-theoretic fibre in the quasi-finite locus. -/
theorem quasiFiniteAt_fiberOver_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (p : FieldValuedPoint Y) :
    (∀ x : Points X, Points.map f x = Points.mk p → QuasiFiniteAt f x) ↔
      ∀ x ∈ fiberOver f (Points.mk p), QuasiFiniteAt f x :=
  sorry

/-- Local quasi-finiteness of the structure morphism of a field-valued fibre is
equivalent to discreteness of its space of points. This is the bridge through
Lemma 68.18.8, not a source-listed condition. -/
theorem locallyQuasiFinite_fieldFiberToSpec_iff {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (p : FieldValuedPoint Y) :
    LocallyQuasiFinite (fieldFiberToSpec f p) ↔
      DiscreteTopology (Points (fieldFiber f p)) :=
  sorry

/-- Local quasi-finiteness of the structure morphism of a field-valued fibre is
equivalent to quasi-finiteness of `f` at every point over the class of `p`. -/
theorem locallyQuasiFinite_fieldFiberToSpec_iff_quasiFiniteAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (p : FieldValuedPoint Y) :
    LocallyQuasiFinite (fieldFiberToSpec f p) ↔
      ∀ x : Points X, Points.map f x = Points.mk p → QuasiFiniteAt f x :=
  sorry

/-- If `Y` is decent, discreteness of the set-theoretic fibre is equivalent to
discreteness of the points of the field-valued fibre. -/
theorem discreteTopology_fiberOver_iff_discreteTopology_fieldFiber
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsDecent Y] (p : FieldValuedPoint Y) :
    DiscreteTopology (fiberOver f (Points.mk p)) ↔
      DiscreteTopology (Points (fieldFiber f p)) :=
  sorry

/-- If `X` and `Y` are decent, finiteness of the set-theoretic fibre implies that
this fibre is discrete. -/
theorem discreteTopology_fiberOver_of_isDecent_finite {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDecent X]
    [IsDecent Y] (p : FieldValuedPoint Y)
    (hF : (fiberOver f (Points.mk p)).Finite) :
    DiscreteTopology (fiberOver f (Points.mk p)) :=
  sorry

/-- If `X` and `Y` are decent, finiteness of the set-theoretic fibre implies that
the points of the field-valued fibre are discrete. -/
theorem discreteTopology_fieldFiber_of_finite_fiberOver {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDecent X]
    [IsDecent Y] (p : FieldValuedPoint Y)
    (hF : (fiberOver f (Points.mk p)).Finite) :
    DiscreteTopology (Points (fieldFiber f p)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
