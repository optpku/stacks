module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic
public import Mathlib.Data.List.TFAE

/-!
# Pointwise finite type of morphisms of algebraic spaces

A morphism of algebraic spaces is of finite type at a point when it is
locally of finite type after restriction to an open subspace neighbourhood,
and its local finite type property admits equivalent pointwise, base-change,
étale-square, and Zariski-cover characterizations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces is of finite type at a
point `x` of `X` if it is locally of finite type after restriction to
some open subspace neighbourhood of `x`. -/
def FiniteTypeAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
    IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧
      LocallyOfFiniteType (i ≫ f)

/-- Finite type at a point is the existence of an open subspace neighbourhood
on which the morphism is locally of finite type. -/
theorem finiteTypeAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    FiniteTypeAt f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧
          LocallyOfFiniteType (i ≫ f) :=
  Iff.rfl

namespace LocallyOfFiniteType

/-- Every base change of `f` along a morphism from a scheme is locally of
finite type. -/
def baseChangeOnSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∀ {Z : Over S} (g : ofOver Z ⟶ Y),
    LocallyOfFiniteType (pullbackAlongScheme.snd f g)

/-- Every base change of `f` along a morphism from an affine scheme is locally
of finite type. -/
def baseChangeOnAffineSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∀ {Z : Over S} (g : ofOver Z ⟶ Y),
    IsAffine Z.left → LocallyOfFiniteType (pullbackAlongScheme.snd f g)

/-- There is a surjective étale morphism from a scheme to `Y` along which the
base change of `f` is locally of finite type. -/
def existsSurjectiveEtaleTarget {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (V : Over S) (b : ofOver V ⟶ Y),
    (over (@AlgebraicGeometry.Etale)).presheaf b ∧
      Surjective b ∧ LocallyOfFiniteType (pullbackAlongScheme.snd f b)

/-- There is a surjective étale morphism `φ` from a scheme to `X` such that
`φ ≫ f` is locally of finite type. -/
def existsSurjectiveEtaleSource {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (U : Over S) (φ : ofOver U ⟶ X),
    (over (@AlgebraicGeometry.Etale)).presheaf φ ∧
      Surjective φ ∧ LocallyOfFiniteType (φ ≫ f)

/-- Every étale scheme square over `f` has locally-of-finite-type top arrow. -/
def forallEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
    (over (@AlgebraicGeometry.Etale)).presheaf a →
      (over (@AlgebraicGeometry.Etale)).presheaf b →
        a ≫ f = yoneda.map h ≫ b →
          AlgebraicGeometry.LocallyOfFiniteType h.left

/-- There is an étale scheme square over `f` with surjective source cover and
locally-of-finite-type top arrow. -/
def existsEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V),
    (over (@AlgebraicGeometry.Etale)).presheaf a ∧
      (over (@AlgebraicGeometry.Etale)).presheaf b ∧
        a ≫ f = ofOverMap h ≫ b ∧
          Surjective a ∧ AlgebraicGeometry.LocallyOfFiniteType h.left

/-- There are Zariski coverings of `Y` and of the inverse images in `X` on which
the pieces of `f` are locally of finite type. -/
def existsZariskiCover {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop :=
  ∃ 𝒱 : ZariskiCover.{u, v} Y, ∀ i : 𝒱.I₀,
    ∃ (Xi : AlgebraicSpace S) (ι : Xi ⟶ X) (_ : IsOpenImmersion ι)
      (𝒰 : ZariskiCover.{u, v} Xi) (h : ∀ j, 𝒰.X j ⟶ 𝒱.X i),
      (∀ j, 𝒰.f j ≫ ι ≫ f = h j ≫ 𝒱.f i) ∧
        (∀ j, LocallyOfFiniteType (h j)) ∧
          Set.range (Points.map ι) =
            (Points.map f) ⁻¹' Set.range (Points.map (𝒱.f i))

end LocallyOfFiniteType

/-- Local finite type of a morphism of algebraic spaces is equivalent to its
pointwise, scheme base-change, affine base-change, étale atlas, étale square,
and Zariski-cover criteria. -/
theorem locallyOfFiniteType_tfae {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    List.TFAE
      [ LocallyOfFiniteType f
      , ∀ x : Points X, FiniteTypeAt f x
      , LocallyOfFiniteType.baseChangeOnSchemes f
      , LocallyOfFiniteType.baseChangeOnAffineSchemes f
      , LocallyOfFiniteType.existsSurjectiveEtaleTarget f
      , LocallyOfFiniteType.existsSurjectiveEtaleSource f
      , LocallyOfFiniteType.forallEtaleSquare f
      , LocallyOfFiniteType.existsEtaleSquare f
      , LocallyOfFiniteType.existsZariskiCover.{u, v} f ] :=
  sorry

namespace LocallyOfFiniteType

/-- A morphism of algebraic spaces is locally of finite type if and only if it is
of finite type at every point. -/
theorem iff_forall_finiteTypeAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : LocallyOfFiniteType f ↔ ∀ x : Points X, FiniteTypeAt f x :=
  (locallyOfFiniteType_tfae.{u, u} f).out 0 1

/-- A morphism of algebraic spaces is locally of finite type if and only if every
base change along a scheme is locally of finite type. -/
theorem iff_baseChangeOnSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : LocallyOfFiniteType f ↔ baseChangeOnSchemes f :=
  (locallyOfFiniteType_tfae.{u, u} f).out 0 2

/-- A morphism of algebraic spaces is locally of finite type if and only if every
base change along an affine scheme is locally of finite type. -/
theorem iff_baseChangeOnAffineSchemes {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : LocallyOfFiniteType f ↔ baseChangeOnAffineSchemes f :=
  (locallyOfFiniteType_tfae.{u, u} f).out 0 3

/-- A morphism of algebraic spaces is locally of finite type if and only if its
base change along some surjective étale scheme atlas of its target is locally of finite type. -/
theorem iff_existsSurjectiveEtaleTarget {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : LocallyOfFiniteType f ↔ existsSurjectiveEtaleTarget f :=
  (locallyOfFiniteType_tfae.{u, u} f).out 0 4

/-- A morphism of algebraic spaces is locally of finite type if and only if its
composite with some surjective étale scheme atlas of its source is locally of finite type. -/
theorem iff_existsSurjectiveEtaleSource {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : LocallyOfFiniteType f ↔ existsSurjectiveEtaleSource f :=
  (locallyOfFiniteType_tfae.{u, u} f).out 0 5

/-- A morphism of algebraic spaces is locally of finite type if and only if every
étale scheme square over it has locally-of-finite-type top arrow. -/
theorem iff_forallEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : LocallyOfFiniteType f ↔ forallEtaleSquare f :=
  (locallyOfFiniteType_tfae.{u, u} f).out 0 6

/-- A morphism of algebraic spaces is locally of finite type if and only if some
étale scheme square over it has surjective source cover and locally-of-finite-type top arrow. -/
theorem iff_existsEtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : LocallyOfFiniteType f ↔ existsEtaleSquare f :=
  (locallyOfFiniteType_tfae.{u, u} f).out 0 7

/-- A morphism of algebraic spaces is locally of finite type if and only if it is
locally of finite type on Zariski coverings of its target and the full inverse images. -/
theorem iff_existsZariskiCover {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : LocallyOfFiniteType f ↔ existsZariskiCover.{u, v} f :=
  (locallyOfFiniteType_tfae.{u, v} f).out 0 8

end LocallyOfFiniteType

end AlgebraicGeometry.AlgebraicSpace
