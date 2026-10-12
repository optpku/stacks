/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_27_6_LocallyQuasiFinite

/-!
# Quasi-finite locus of a morphism of algebraic spaces

For a locally of finite type morphism of algebraic spaces, the set of points
at which the morphism is quasi-finite is open, and this locus commutes with
base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The set of points at which a locally of finite type morphism of algebraic
spaces is quasi-finite is open. -/
theorem isOpen_quasiFiniteAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] : IsOpen (setOf (QuasiFiniteAt f)) :=
  sorry

/-- In a cartesian square, a locally of finite type morphism is quasi-finite at
the image of a point if and only if the base-changed morphism is quasi-finite
at that point. -/
theorem quasiFiniteAt_iff_of_isPullback {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hpb : IsPullback g' f' f g) [LocallyOfFiniteType f]
    (x' : Points X') :
    QuasiFiniteAt f' x' ↔ QuasiFiniteAt f (Points.map g' x') :=
  sorry

/-- In a cartesian square, the quasi-finite locus of the base-changed morphism
is the preimage of the original quasi-finite locus. -/
theorem quasiFiniteAt_locus_eq_preimage_of_isPullback {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hpb : IsPullback g' f' f g) [LocallyOfFiniteType f] :
    setOf (QuasiFiniteAt f') = Points.map g' ⁻¹' setOf (QuasiFiniteAt f) :=
  sorry

/-- The quasi-finite locus of `pullback.snd f g` is the preimage of the
quasi-finite locus of `f` along `pullback.fst f g`. -/
theorem quasiFiniteAt_locus_pullback_snd {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : Y' ⟶ Y) [HasPullback f g] :
    setOf (QuasiFiniteAt (pullback.snd f g)) =
      Points.map (pullback.fst f g) ⁻¹' setOf (QuasiFiniteAt f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
