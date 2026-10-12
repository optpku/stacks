/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_27_6_LocallyQuasiFinite
public import stacks_project.Chap67.Lemma_67_34_7_QuasiFiniteLocus

/-!
# Quasi-finiteness at a point of a field fibre of an algebraic space

A locally finite-type morphism of algebraic spaces is quasi-finite at the
image of a zero-dimensional point of a field fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.34.8: Let `S` be a scheme. Consider a cartesian square
`IsPullback p q f g.hom` of algebraic spaces over `S`, with `p : F ⟶ X`,
`f : X ⟶ Y` locally of finite type, and `g : FieldValuedPoint Y` giving
the morphism `Spec(k) ⟶ Y` from the spectrum of a field over `S`. If
`z : Points F` satisfies `dimensionAt z = 0`, then after replacing `X` by
an open subspace containing `Points.map p z` the morphism `X ⟶ Y` is
locally quasi-finite, i.e. `QuasiFiniteAt f (Points.map p z)`. -/
@[stacks 06LS]
theorem quasiFiniteAt_of_dimensionAt_eq_zero {S : Scheme.{u}}
    {X Y F : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : FieldValuedPoint Y) (p : F ⟶ X) (q : F ⟶ ofOver g.overObj)
    (hpb : IsPullback p q f g.hom) (z : Points F)
    (hz : dimensionAt z = (0 : WithBot ℕ∞)) :
    QuasiFiniteAt f (Points.map p z) :=
  sorry

/-- Specialization of `quasiFiniteAt_of_dimensionAt_eq_zero` to the canonical
pullback fibre of `f` over a field-valued point of `Y`. -/
theorem quasiFiniteAt_of_dimensionAt_eq_zero_pullback {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : FieldValuedPoint Y) [HasPullback f g.hom]
    (z : Points (pullback f g.hom))
    (hz : dimensionAt z = (0 : WithBot ℕ∞)) :
    QuasiFiniteAt f (Points.map (pullback.fst f g.hom) z) :=
  sorry

/-- If a point of a field fibre of `f` has dimension zero, then its image in
`X` lies on the quasi-finite locus of `f`. -/
theorem mem_quasiFiniteLocus_of_dimensionAt_eq_zero {S : Scheme.{u}}
    {X Y F : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : FieldValuedPoint Y) (p : F ⟶ X) (q : F ⟶ ofOver g.overObj)
    (hpb : IsPullback p q f g.hom) (z : Points F)
    (hz : dimensionAt z = (0 : WithBot ℕ∞)) :
    Points.map p z ∈ Set.range (Points.map (quasiFiniteLocus f).ι) :=
  sorry

/-- If a point of a field fibre of `f` has dimension zero, there is an open
immersion into `X` through the image of that point along which `f` is
locally quasi-finite. -/
theorem quasiFiniteAt_of_dimensionAt_eq_zero_spec {S : Scheme.{u}}
    {X Y F : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : FieldValuedPoint Y) (p : F ⟶ X) (q : F ⟶ ofOver g.overObj)
    (hpb : IsPullback p q f g.hom) (z : Points F)
    (hz : dimensionAt z = (0 : WithBot ℕ∞)) :
    ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
      IsOpenImmersion i ∧ Points.map p z ∈ Set.range (Points.map i) ∧
        LocallyQuasiFinite (i ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
