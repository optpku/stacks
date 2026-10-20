module

public import ReasLib.RingTheory.Algebra.CardinalGeneration
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineEtaleCover
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeFunctor

/-!
# Cardinal size conditions on algebraic spaces

Affine étale atlas bounds and bounds on algebra generators define countable
locally finite type morphisms and morphisms of a specified cardinal type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space is covered by at most `κ` affine schemes étale over it. -/
def CoveredByCardinalAffines {S : Scheme.{u}} (X : AlgebraicSpace S)
    (κ : Cardinal.{u}) : Prop :=
  ∃ 𝒰 : AffineEtaleCover.{u, u} X, Cardinal.mk 𝒰.I ≤ κ

/-- An affine étale cover of index cardinality at most `κ` witnesses
`CoveredByCardinalAffines`. -/
theorem coveredByCardinalAffines_iff {S : Scheme.{u}} (X : AlgebraicSpace S)
    (κ : Cardinal.{u}) :
    CoveredByCardinalAffines X κ ↔
      ∃ 𝒰 : AffineEtaleCover.{u, u} X, Cardinal.mk 𝒰.I ≤ κ :=
  Iff.rfl

/-- An affine algebraic space is covered by at most `κ` affine schemes étale
over it whenever `ℵ₀ ≤ κ`. -/
theorem coveredByCardinalAffines_of_isAffine {S : Scheme.{u}}
    {X : AlgebraicSpace S} {κ : Cardinal.{u}} [IsAffine X]
    (hκ : Cardinal.aleph0 ≤ κ) :
    CoveredByCardinalAffines X κ :=
  sorry

/-- An algebraic space is covered by countably many affine schemes étale over
it. -/
def CoveredByCountablyManyAffines {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Prop :=
  ∃ 𝒰 : AffineEtaleCover.{u, u} X, Countable 𝒰.I

/-- A countable affine étale cover witnesses
`CoveredByCountablyManyAffines`. -/
theorem coveredByCountablyManyAffines_iff {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    CoveredByCountablyManyAffines X ↔
      ∃ 𝒰 : AffineEtaleCover.{u, u} X, Countable 𝒰.I :=
  Iff.rfl

/-- An affine algebraic space is covered by countably many affines. -/
theorem coveredByCountablyManyAffines_of_isAffine {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsAffine X] : CoveredByCountablyManyAffines X :=
  sorry

/-- An affine étale cover of cardinality at most `ℵ₀` is a countable affine
étale cover. -/
theorem coveredByCountablyManyAffines_of_cardinal {S : Scheme.{u}}
    {X : AlgebraicSpace S} {κ : Cardinal.{u}}
    (h : CoveredByCardinalAffines X κ) (hκ : κ ≤ Cardinal.aleph0) :
    CoveredByCountablyManyAffines X :=
  sorry

/-- The inverse image in `X` of an open of `U` along `f : X ⟶ ofOver U`. -/
def inverseImageAlongOpen {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ ofOver U) (W : U.left.Opens) : AlgebraicSpace S :=
  pullbackAlongScheme f ((ofOverFunctor S).map
    (Over.homMk W.ι : Over.mk (W.ι ≫ U.hom) ⟶ U))

/-- A morphism `X ⟶ ofOver U` is locally of finite type with countable affine
étale inverse images of affine opens of `U`. -/
class CountablyAffineLocallyOfFiniteType {S : Scheme.{u}}
    {X : AlgebraicSpace S} {U : Over S} (f : X ⟶ ofOver U) : Prop
    extends LocallyOfFiniteType f where
  /-- The inverse image of every affine open of `U` has a countable affine
  étale cover. -/
  of_affineOpen {W : U.left.Opens} (hW : IsAffineOpen W) :
    CoveredByCountablyManyAffines (inverseImageAlongOpen f W)

namespace CountablyAffineLocallyOfFiniteType

/-- The two defining conditions of `CountablyAffineLocallyOfFiniteType`. -/
theorem iff {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ ofOver U) :
    CountablyAffineLocallyOfFiniteType f ↔
      LocallyOfFiniteType f ∧
        ∀ {W : U.left.Opens}, IsAffineOpen W →
          CoveredByCountablyManyAffines (inverseImageAlongOpen f W) := by
  constructor
  · intro h
    exact ⟨h.toLocallyOfFiniteType, h.of_affineOpen⟩
  · rintro ⟨hfinite, hcover⟩
    exact { toLocallyOfFiniteType := hfinite, of_affineOpen := hcover }

/-- Inverse images of affine opens along a countable locally finite type
morphism have countable affine covers. -/
theorem spec_of_affineOpen {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : Over S} (f : X ⟶ ofOver U) [CountablyAffineLocallyOfFiniteType f]
    {W : U.left.Opens} (hW : IsAffineOpen W) :
    CoveredByCountablyManyAffines (inverseImageAlongOpen f W) :=
  of_affineOpen hW

/-- The identity of `ofOver U` is locally of finite type with countable affine
inverse images. -/
instance id {S : Scheme.{u}} {U : Over S} :
    CountablyAffineLocallyOfFiniteType (𝟙 (ofOver U)) :=
  sorry

/-- A finite type morphism `X ⟶ ofOver U` satisfies the countable affine
locally finite type cut. -/
instance of_finiteType {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (f : X ⟶ ofOver U) [FiniteType f] :
    CountablyAffineLocallyOfFiniteType f :=
  sorry

end CountablyAffineLocallyOfFiniteType

/-- A morphism of algebraic spaces is of `κ`-type when étale scheme squares have
ring extensions generated by at most `κ` elements and inverse images of affine
schemes have an affine étale atlas of cardinality at most `κ`. -/
class OfCardinalType (κ : Cardinal.{u}) {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- Étale scheme squares have `κ`-bounded generation on affine opens. -/
  of_etale {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
      (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
      (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
      (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
      (w : a ≫ f = yoneda.map h ≫ b) {W : V.left.Opens}
      (hW : IsAffineOpen W) {Z : U.left.Opens} (hZ : IsAffineOpen Z)
      (e : Z ≤ h.left ⁻¹ᵁ W) :
    RingHom.generatorsBounded κ (h.left.appLE W Z e).hom
  /-- Inverse images of affine schemes have an affine étale atlas of
  cardinality at most `κ`. -/
  of_affine {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
      (g : ofOver Z ⟶ Y) :
    CoveredByCardinalAffines (pullbackAlongScheme f g) κ

namespace OfCardinalType

/-- The two defining conditions of `OfCardinalType`. -/
theorem iff {κ : Cardinal.{u}} {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    OfCardinalType κ f ↔
      (∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
          (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
          (over (@AlgebraicGeometry.Etale)).presheaf a →
            (over (@AlgebraicGeometry.Etale)).presheaf b →
              a ≫ f = yoneda.map h ≫ b →
                ∀ {W : V.left.Opens}, IsAffineOpen W →
                  ∀ {Z : U.left.Opens}, IsAffineOpen Z →
                    ∀ (e : Z ≤ h.left ⁻¹ᵁ W),
                      RingHom.generatorsBounded κ (h.left.appLE W Z e).hom) ∧
        ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
          (g : ofOver Z ⟶ Y),
          CoveredByCardinalAffines (pullbackAlongScheme f g) κ := by
  constructor
  · intro h
    exact ⟨h.of_etale, h.of_affine⟩
  · rintro ⟨hgen, hcover⟩
    exact ⟨hgen, hcover⟩

/-- The generator-bound field of a morphism of `κ`-type. -/
theorem spec_of_etale {κ : Cardinal.{u}} {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [OfCardinalType κ f]
    {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = yoneda.map h ≫ b) {W : V.left.Opens} (hW : IsAffineOpen W)
    {Z : U.left.Opens} (hZ : IsAffineOpen Z) (e : Z ≤ h.left ⁻¹ᵁ W) :
    RingHom.generatorsBounded κ (h.left.appLE W Z e).hom :=
  of_etale a b h ha hb w hW hZ e

/-- The affine-cover field of a morphism of `κ`-type. -/
theorem spec_of_affine {κ : Cardinal.{u}} {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [OfCardinalType κ f] {Z : Over S}
    [AlgebraicGeometry.IsAffine Z.left] (g : ofOver Z ⟶ Y) :
    CoveredByCardinalAffines (pullbackAlongScheme f g) κ :=
  of_affine g

/-- The identity morphism is of `κ`-type whenever `ℵ₀ ≤ κ`. -/
instance id {κ : Cardinal.{u}} {S : Scheme.{u}} {X : AlgebraicSpace S}
    [hκ : Fact (Cardinal.aleph0 ≤ κ)] : OfCardinalType κ (𝟙 X) :=
  sorry

end OfCardinalType

end AlgebraicGeometry.AlgebraicSpace
