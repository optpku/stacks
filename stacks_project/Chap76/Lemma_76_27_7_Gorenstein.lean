/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein.Locus
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap76.Lemma_76_27_6_GorensteinAt

/-!
# Gorenstein locus of a morphism of algebraic spaces

The Gorenstein locus of a morphism of algebraic spaces is the set of points
at which the morphism is Gorenstein in the sense of `GorensteinAt`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace GorensteinAt

/-- A morphism satisfying `GorensteinAt f x` admits an étale scheme square
through `x` whose top arrow is Gorenstein at the corresponding germ. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {x : Points X} (h : GorensteinAt f x) :
    ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
      (u : U.left),
      (over (@AlgebraicGeometry.Etale)).presheaf a ∧
        (over (@AlgebraicGeometry.Etale)).presheaf b ∧
          a ≫ f = ofOverMap h ≫ b ∧
            Points.map a (ofOver.pointsEquiv U u) = x ∧
              Scheme.Hom.gorensteinAt h.left u :=
  sorry

end GorensteinAt

/-- The locus of points of `X` at which `f` is Gorenstein. -/
def gorensteinLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Set (Points X) :=
  {x | GorensteinAt f x}

/-- A point lies in the Gorenstein locus exactly when the morphism is
Gorenstein at that point. -/
theorem mem_gorensteinLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    x ∈ gorensteinLocus f ↔ GorensteinAt f x :=
  sorry

/-- Along an étale scheme square over `f`, the preimage of `gorensteinLocus f`
is the scheme-level Gorenstein locus of the top arrow. -/
theorem mapOfOver_preimage_gorensteinLocus {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) {U V : Over S} (a : ofOver U ⟶ X)
    (b : ofOver V ⟶ Y) (h : U ⟶ V)
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) :
    Points.mapOfOver a ⁻¹' gorensteinLocus f =
      Scheme.Hom.gorensteinLocus h.left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
