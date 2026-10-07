module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap65.Definition_65_12_5_ZariskiCover
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Definition_67_5_2_Surjective

/-!
# Smooth morphisms of algebraic spaces

A morphism of algebraic spaces is smooth when every étale scheme square over it
has smooth top arrow, in the sense of Stacks Definition 67.37.1 (1).
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` is smooth if every
commutative square with étale vertical arrows from schemes has smooth top
arrow. -/
class Smooth {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- Every étale scheme square over `f` has smooth top arrow. -/
  of_etale {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
      (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
      (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
      (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
      (w : a ≫ f = yoneda.map h ≫ b) :
    AlgebraicGeometry.Smooth h.left

/-- A morphism of algebraic spaces is smooth if and only if every commutative
square with étale vertical arrows from schemes has smooth top arrow. -/
theorem smooth_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Smooth f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b → AlgebraicGeometry.Smooth h.left :=
  sorry

namespace Smooth

/-- An étale scheme square over a smooth morphism of algebraic spaces has smooth
top arrow. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Smooth f]
    {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = yoneda.map h ≫ b) : AlgebraicGeometry.Smooth h.left :=
  sorry

/-- The identity morphism of an algebraic space is smooth. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Smooth (𝟙 X) :=
  sorry

end Smooth

/-- A morphism `f : X ⟶ Y` of algebraic spaces is smooth at a point `x` of `X`
if it is smooth after restriction to some open subspace neighbourhood of `x`. -/
def SmoothAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
    IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ Smooth (i ≫ f)

/-- Smoothness at a point is the existence of an open subspace neighbourhood on
which the morphism is smooth. -/
theorem smoothAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) :
    SmoothAt f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ Smooth (i ≫ f) :=
  sorry

/-- Functor-of-points pullbacks exist in the presheaf category on schemes over `S`. -/
instance hasPullbacks_over_presheaf (S : Scheme.{u}) :
    HasPullbacks ((Over S)ᵒᵖ ⥤ Type u) := inferInstance

/-- The functor of points of the fibre product of `X` with a scheme over `Y`. -/
def pullbackAlongSchemeFunctorOfPoints {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {V : Over S} (b : ofOver V ⟶ Y) : (Over S)ᵒᵖ ⥤ Type u :=
  let fP : X.functorOfPoints ⟶ Y.functorOfPoints := f
  let bP : (ofOver V).functorOfPoints ⟶ Y.functorOfPoints := b
  pullback fP bP

/-- The first projection of the functor-of-points fibre product. -/
def pullbackAlongSchemeFstNat {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {V : Over S} (b : ofOver V ⟶ Y) :
    pullbackAlongSchemeFunctorOfPoints f b ⟶ X.functorOfPoints :=
  let fP : X.functorOfPoints ⟶ Y.functorOfPoints := f
  let bP : (ofOver V).functorOfPoints ⟶ Y.functorOfPoints := b
  pullback.fst fP bP

/-- The second projection of the functor-of-points fibre product. -/
def pullbackAlongSchemeSndNat {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {V : Over S} (b : ofOver V ⟶ Y) :
    pullbackAlongSchemeFunctorOfPoints f b ⟶ (ofOver V).functorOfPoints :=
  let fP : X.functorOfPoints ⟶ Y.functorOfPoints := f
  let bP : (ofOver V).functorOfPoints ⟶ Y.functorOfPoints := b
  pullback.snd fP bP

/-- The fibre product `V ×_Y X` of an algebraic space morphism `f : X ⟶ Y` with
a morphism from a scheme `V` over `S`. -/
def pullbackAlongScheme {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {V : Over S} (b : ofOver V ⟶ Y) : AlgebraicSpace S :=
  ofFunctor (pullbackAlongSchemeFunctorOfPoints f b) sorry sorry sorry

namespace pullbackAlongScheme

/-- The projection `V ×_Y X ⟶ X`. -/
def fst {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) {V : Over S}
    (b : ofOver V ⟶ Y) : pullbackAlongScheme f b ⟶ X :=
  pullbackAlongSchemeFstNat f b

/-- The projection `V ×_Y X ⟶ V`. -/
def snd {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) {V : Over S}
    (b : ofOver V ⟶ Y) : pullbackAlongScheme f b ⟶ ofOver V :=
  pullbackAlongSchemeSndNat f b

/-- The functor of points of `pullbackAlongScheme f b` is the presheaf pullback. -/
theorem functorOfPoints_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {V : Over S} (b : ofOver V ⟶ Y) :
    (pullbackAlongScheme f b).functorOfPoints =
      pullbackAlongSchemeFunctorOfPoints f b :=
  sorry

/-- The two projections of `pullbackAlongScheme f b` commute with `f` and `b`. -/
theorem fst_comp {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {V : Over S} (b : ofOver V ⟶ Y) : fst f b ≫ f = snd f b ≫ b :=
  sorry

/-- `V ×_Y X` is a fibre product of `f` and a morphism from a scheme over `Y`. -/
theorem isPullback {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {V : Over S} (b : ofOver V ⟶ Y) :
    IsPullback (fst f b) (snd f b) f b :=
  sorry

end pullbackAlongScheme

namespace Smooth

/-- Every base change of `f` along a morphism from a scheme is smooth. -/
def baseChangeOnSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∀ {Z : Over S} (g : ofOver Z ⟶ Y), Smooth (pullbackAlongScheme.snd f g)

/-- Every base change of `f` along a morphism from an affine scheme is smooth. -/
def baseChangeOnAffineSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∀ {Z : Over S} (g : ofOver Z ⟶ Y),
    IsAffine Z.left → Smooth (pullbackAlongScheme.snd f g)

/-- There is a surjective étale morphism from a scheme to `Y` along which the
base change of `f` is smooth. -/
def existsSurjectiveEtaleTarget {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (V : Over S) (b : ofOver V ⟶ Y),
    (over (@AlgebraicGeometry.Etale)).presheaf b ∧
      Surjective b ∧ Smooth (pullbackAlongScheme.snd f b)

/-- There is a surjective étale morphism `φ` from a scheme to `X` such that
`φ ≫ f` is smooth. -/
def existsSurjectiveEtaleSource {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (U : Over S) (φ : ofOver U ⟶ X),
    (over (@AlgebraicGeometry.Etale)).presheaf φ ∧ Surjective φ ∧ Smooth (φ ≫ f)

/-- Every étale scheme square over `f` has smooth top arrow. -/
def forallEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
    (over (@AlgebraicGeometry.Etale)).presheaf a →
      (over (@AlgebraicGeometry.Etale)).presheaf b →
        a ≫ f = yoneda.map h ≫ b → AlgebraicGeometry.Smooth h.left

/-- There is an étale scheme square over `f` with surjective source cover and
smooth top arrow. -/
def existsEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V),
    (over (@AlgebraicGeometry.Etale)).presheaf a ∧
      (over (@AlgebraicGeometry.Etale)).presheaf b ∧
        a ≫ f = ofOverMap h ≫ b ∧
          Surjective a ∧ AlgebraicGeometry.Smooth h.left

/-- There are Zariski coverings of `Y` and of the inverse images in `X` on which
the pieces of `f` are smooth. -/
def existsZariskiCover {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∃ 𝒱 : ZariskiCover.{u, v} Y, ∀ i : 𝒱.I₀,
    ∃ (Xi : AlgebraicSpace S) (ι : Xi ⟶ X) (_ : IsOpenImmersion ι)
      (𝒰 : ZariskiCover.{u, v} Xi) (h : ∀ j, 𝒰.X j ⟶ 𝒱.X i),
      (∀ j, 𝒰.f j ≫ ι ≫ f = h j ≫ 𝒱.f i) ∧
        (∀ j, Smooth (h j)) ∧
          ∀ x : Points X,
            Points.map f x ∈ Set.range (Points.map (𝒱.f i)) →
              x ∈ Set.range (Points.map ι)

end Smooth

end AlgebraicGeometry.AlgebraicSpace
