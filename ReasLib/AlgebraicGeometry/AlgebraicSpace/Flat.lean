module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat

/-!
# Flat morphisms of algebraic spaces

The flatness class and its étale-square API are owned by `Morphism.Flat`.
Flatness is equivalent to pointwise flatness and can be tested after scheme
base change, on étale presentations, or on Zariski coverings.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces is flat at a point `x` of `X` if
some étale scheme square over `f` has top arrow flat at a point of `U` mapping
to `x`. -/
def FlatAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
    (u : U.left),
    (over (@AlgebraicGeometry.Etale)).presheaf a ∧
      (over (@AlgebraicGeometry.Etale)).presheaf b ∧
        a ≫ f = ofOverMap h ≫ b ∧
          Points.map a (ofOver.pointsEquiv U u) = x ∧
            Scheme.Hom.flatAt h.left u

/-- Flatness at a point is the existence of an étale scheme presentation whose
top arrow is flat at a germ mapping to that point. -/
theorem flatAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) :
    FlatAt f x ↔
      ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
        (u : U.left),
        (over (@AlgebraicGeometry.Etale)).presheaf a ∧
          (over (@AlgebraicGeometry.Etale)).presheaf b ∧
            a ≫ f = ofOverMap h ≫ b ∧
              Points.map a (ofOver.pointsEquiv U u) = x ∧
                Scheme.Hom.flatAt h.left u :=
  Iff.rfl

/-- A morphism of schemes over `S`, viewed as a morphism of algebraic spaces, is
flat if and only if the underlying morphism of schemes is flat. -/
theorem flat_ofOverMap_iff {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V) :
    Flat (ofOverMap h) ↔ AlgebraicGeometry.Flat h.left :=
  sorry

namespace Flat

/-- Every base change of `f` along a morphism from a scheme is flat. -/
def baseChangeOnSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∀ {Z : Over S} (g : ofOver Z ⟶ Y), Flat (pullbackAlongScheme.snd f g)

/-- Every base change of `f` along a morphism from an affine scheme is flat. -/
def baseChangeOnAffineSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∀ {Z : Over S} (g : ofOver Z ⟶ Y),
    IsAffine Z.left → Flat (pullbackAlongScheme.snd f g)

/-- There is a surjective étale morphism from a scheme to `Y` along which the
base change of `f` is flat. -/
def existsSurjectiveEtaleTarget {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (V : Over S) (b : ofOver V ⟶ Y),
    (over (@AlgebraicGeometry.Etale)).presheaf b ∧
      Surjective b ∧ Flat (pullbackAlongScheme.snd f b)

/-- There is a surjective étale morphism `φ` from a scheme to `X` such that
`φ ≫ f` is flat. -/
def existsSurjectiveEtaleSource {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (U : Over S) (φ : ofOver U ⟶ X),
    (over (@AlgebraicGeometry.Etale)).presheaf φ ∧ Surjective φ ∧ Flat (φ ≫ f)

/-- Every étale scheme square over `f` has flat top arrow. -/
def forallEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
    (over (@AlgebraicGeometry.Etale)).presheaf a →
      (over (@AlgebraicGeometry.Etale)).presheaf b →
        a ≫ f = yoneda.map h ≫ b → AlgebraicGeometry.Flat h.left

/-- There is an étale scheme square over `f` with surjective source cover and
flat top arrow. -/
def existsEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V),
    (over (@AlgebraicGeometry.Etale)).presheaf a ∧
      (over (@AlgebraicGeometry.Etale)).presheaf b ∧
        a ≫ f = ofOverMap h ≫ b ∧
          Surjective a ∧ AlgebraicGeometry.Flat h.left

/-- There are Zariski coverings of `Y` and of the inverse images in `X` on which
the pieces of `f` are flat. -/
def existsZariskiCover {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∃ 𝒱 : ZariskiCover.{u, v} Y, ∀ i : 𝒱.I₀,
    ∃ (Xi : AlgebraicSpace S) (ι : Xi ⟶ X) (_ : IsOpenImmersion ι)
      (𝒰 : ZariskiCover.{u, v} Xi) (h : ∀ j, 𝒰.X j ⟶ 𝒱.X i),
      (∀ j, 𝒰.f j ≫ ι ≫ f = h j ≫ 𝒱.f i) ∧
        (∀ j, Flat (h j)) ∧
          Set.range (Points.map ι) = (Points.map f) ⁻¹' Set.range (Points.map (𝒱.f i))

end Flat

/-- Flatness of a morphism of algebraic spaces is equivalent to pointwise
flatness, flatness after every scheme or affine-scheme base change, flatness
on a surjective étale target or source presentation, the universal or
existential étale scheme-square condition, and flatness on Zariski coverings
of the target and its inverse images. -/
theorem flat_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    List.TFAE
      [ Flat f
      , ∀ x : Points X, FlatAt f x
      , Flat.baseChangeOnSchemes f
      , Flat.baseChangeOnAffineSchemes f
      , Flat.existsSurjectiveEtaleTarget f
      , Flat.existsSurjectiveEtaleSource f
      , Flat.forallEtaleSquare f
      , Flat.existsEtaleSquare f
      , Flat.existsZariskiCover.{u, v} f ] :=
  sorry

/-- A morphism of algebraic spaces is flat if and only if it is flat at every
point of its source. -/
theorem flat_iff_forall_flatAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Flat f ↔ ∀ x : Points X, FlatAt f x :=
  (flat_tfae.{u, u} f).out 0 1

end AlgebraicGeometry.AlgebraicSpace
