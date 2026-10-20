module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap67.Lemma_67_37_4_Smooth

/-!
# Flat morphisms of algebraic spaces

A morphism of algebraic spaces is flat when every étale scheme square over it
has flat top arrow, in the sense of Stacks Definition 67.30.1 (1). Flatness at
a point is the presentation-wise germ condition of Definition 67.30.1 (2).
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.FlatAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X), Prop)

/- Flatness at a point is the existence of an étale scheme presentation whose
top arrow is flat at a germ mapping to that point. -/
#check (AlgebraicGeometry.AlgebraicSpace.flatAt_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X),
    FlatAt f x ↔
      ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
        (u : U.left),
        (over (@AlgebraicGeometry.Etale)).presheaf a ∧
          (over (@AlgebraicGeometry.Etale)).presheaf b ∧
            a ≫ f = ofOverMap h ≫ b ∧
              Points.map a (ofOver.pointsEquiv U u) = x ∧
                Scheme.Hom.flatAt h.left u)

/- A morphism of schemes over `S`, viewed as a morphism of algebraic spaces, is
flat if and only if the underlying morphism of schemes is flat. -/
#check (AlgebraicGeometry.AlgebraicSpace.flat_ofOverMap_iff :
  ∀ {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V),
    Flat (ofOverMap h) ↔ AlgebraicGeometry.Flat h.left)

namespace Flat

/- Every base change of `f` along a morphism from a scheme is flat. -/
#check (AlgebraicGeometry.AlgebraicSpace.Flat.baseChangeOnSchemes :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)

/- Every base change of `f` along a morphism from an affine scheme is flat. -/
#check (AlgebraicGeometry.AlgebraicSpace.Flat.baseChangeOnAffineSchemes :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)

/- There is a surjective étale morphism from a scheme to `Y` along which the
base change of `f` is flat. -/
#check (AlgebraicGeometry.AlgebraicSpace.Flat.existsSurjectiveEtaleTarget :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)

/- There is a surjective étale morphism `φ` from a scheme to `X` such that
`φ ≫ f` is flat. -/
#check (AlgebraicGeometry.AlgebraicSpace.Flat.existsSurjectiveEtaleSource :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)

/- Every étale scheme square over `f` has flat top arrow. -/
#check (AlgebraicGeometry.AlgebraicSpace.Flat.forallEtaleSquare :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)

/- There is an étale scheme square over `f` with surjective source cover and
flat top arrow. -/
#check (AlgebraicGeometry.AlgebraicSpace.Flat.existsEtaleSquare :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)

/- There are Zariski coverings of `Y` and of the inverse images in `X` on which
the pieces of `f` are flat. -/
#check (AlgebraicGeometry.AlgebraicSpace.Flat.existsZariskiCover.{u, v} :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)

end Flat

end AlgebraicGeometry.AlgebraicSpace
