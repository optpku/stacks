module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Definition 67.27.1 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is locally quasi-finite if the equivalent conditions of Lemma 67.22.1 hold
with `P` equal to locally quasi-finite, i.e. locally of finite type and locally
quasi-finite. -/
@[stacks 03XJ] #check (AlgebraicGeometry.AlgebraicSpace.FiniteType.locallyQuasiFinite_iff :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y),
    LocallyOfFiniteType f ∧ LocallyQuasiFinite f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b →
              AlgebraicGeometry.LocallyOfFiniteType h.left ∧
                AlgebraicGeometry.LocallyQuasiFinite h.left)

/- Definition 67.27.1 (2): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is quasi-finite at a point `x` of `|X|` if some open neighbourhood `X' ⊂ X`
of `x` has locally quasi-finite restriction `f|_{X'} : X' ⟶ Y`. -/
@[stacks 03XJ] #check (AlgebraicGeometry.AlgebraicSpace.FiniteType.QuasiFiniteAt :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X), Prop)

/- Definition 67.27.1 (3): a morphism of algebraic spaces `f : X ⟶ Y` is
quasi-finite if it is locally quasi-finite and quasi-compact. -/
@[stacks 03XJ] #check (AlgebraicGeometry.AlgebraicSpace.QuasiFinite :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

end AlgebraicGeometry.AlgebraicSpace
