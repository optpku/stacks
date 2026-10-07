module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocal
public import stacks_project.Chap65.Definition_65_6_3_Hom

/-!
# Étale-local lifts of scheme morphism properties to algebraic spaces

A property of morphisms of schemes that is étale local on source-and-target
lifts to morphisms of algebraic spaces by asking that every étale scheme square
has top arrow satisfying the original property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- The lift of a scheme-morphism property `P` that is étale local on
source-and-target to morphisms of algebraic spaces over `S`: every commutative
square with étale vertical arrows from schemes has top arrow satisfying `P`. -/
#check (AlgebraicGeometry.AlgebraicSpace.etaleLocal :
  ∀ {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    [IsEtaleLocalAtSourceAndTarget P], MorphismProperty (AlgebraicSpace S))

/- A morphism of algebraic spaces has the lift of `P` if and only if every
commutative square with étale vertical arrows from schemes has top arrow
satisfying `P`. -/
#check (AlgebraicGeometry.AlgebraicSpace.etaleLocal_iff :
  ∀ {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    [IsEtaleLocalAtSourceAndTarget P] {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    etaleLocal P f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b → P h.left)

/- An étale scheme square over a morphism of algebraic spaces having the lift of
`P` has top arrow satisfying `P`. -/
#check (AlgebraicGeometry.AlgebraicSpace.etaleLocal_spec :
  ∀ {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    [IsEtaleLocalAtSourceAndTarget P] {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : etaleLocal P f) {U V : Over S}
    (a : yoneda.obj U ⟶ X.functorOfPoints) (b : yoneda.obj V ⟶ Y.functorOfPoints)
    (h : U ⟶ V) (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = yoneda.map h ≫ b), P h.left)

end AlgebraicGeometry.AlgebraicSpace
