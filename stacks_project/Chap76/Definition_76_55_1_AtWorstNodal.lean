module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AtWorstNodal
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Remark_67_22_3_EtaleLocal

/-!
# At-worst-nodal morphisms of algebraic spaces

A morphism of algebraic spaces is at-worst-nodal of relative dimension 1 when
every étale scheme square over it has at-worst-nodal top arrow, in the sense of
Stacks Definition 76.55.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` is at-worst-nodal of
relative dimension 1 if every commutative square with étale vertical arrows from
schemes has at-worst-nodal top arrow. -/
class AtWorstNodal {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- Every étale scheme square over `f` has at-worst-nodal top arrow. -/
  of_etale {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
      (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
      (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
      (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
      (w : a ≫ f = yoneda.map h ≫ b) :
    AlgebraicGeometry.AtWorstNodal h.left

/-- A morphism of algebraic spaces is at-worst-nodal of relative dimension 1 if
and only if every commutative square with étale vertical arrows from schemes has
at-worst-nodal top arrow. -/
theorem atWorstNodal_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    AtWorstNodal f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b → AlgebraicGeometry.AtWorstNodal h.left :=
  sorry

namespace AtWorstNodal

/-- An étale scheme square over an at-worst-nodal morphism of algebraic spaces
has at-worst-nodal top arrow. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AtWorstNodal f] {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = yoneda.map h ≫ b) : AlgebraicGeometry.AtWorstNodal h.left :=
  sorry

/-- A representable morphism of algebraic spaces with the relative
at-worst-nodal property is at-worst-nodal of relative dimension 1. -/
theorem of_presheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : (over
        (@AlgebraicGeometry.AtWorstNodal :
          MorphismProperty Scheme.{u})).presheaf f) :
    AtWorstNodal f :=
  sorry

end AtWorstNodal

/-- A morphism of schemes over `S` that is at-worst-nodal of relative dimension 1
remains at-worst-nodal as a morphism of algebraic spaces via `ofOverMap`. -/
instance instOfOverMap {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V)
    [AlgebraicGeometry.AtWorstNodal h.left] : AtWorstNodal (ofOverMap h) :=
  sorry

/-- A morphism of algebraic spaces is at-worst-nodal of relative dimension 1 if
and only if it has the étale-local lift of scheme-level at-worst-nodality. -/
theorem atWorstNodal_iff_etaleLocal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    [IsEtaleLocalAtSourceAndTarget
      (@AlgebraicGeometry.AtWorstNodal : MorphismProperty Scheme.{u})] :
    AtWorstNodal f ↔
      etaleLocal
        (@AlgebraicGeometry.AtWorstNodal : MorphismProperty Scheme.{u}) f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
