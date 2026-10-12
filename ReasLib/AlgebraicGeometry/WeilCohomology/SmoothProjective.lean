/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Properties
public import ReasLib.AlgebraicGeometry.ChowMotive.Duality

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u w y z

namespace WeilCohomology

/-- A presentation of the category of smooth projective varieties over `k`, together
with its geometric dimension, products, point object, and integral Chow operations. -/
structure SmoothProjectiveContext
    (k : Type u) [Field k] (V : Type w) [Category.{z} V]
    (dimension : V → ℕ) (product : V → V → V)
    (fst : ∀ X Y, product X Y ⟶ X) (snd : ∀ X Y, product X Y ⟶ Y)
    (point : V) (CH : V → Type y) [∀ X, CommRing (CH X)]
    (CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)) [∀ X, GradedAlgebra (CHgrade X)]
    (cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X)
    (cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y)
    (pointCycle : CHgrade point 0) where
  /-- The functor realizing the abstract domain as schemes over `k`. -/
  scheme : V ⥤ SchemeOverField k
  /-- Morphisms in the presentation are precisely morphisms of the represented schemes. -/
  scheme_fullyFaithful : scheme.FullyFaithful
  /-- Every represented object is a variety over `k`. -/
  variety : ∀ X, Variety (scheme.obj X)
  /-- Every represented variety is smooth over `k`. -/
  smooth : ∀ X, Smooth (scheme.obj X).hom
  /-- Every represented variety is projective over `k`. -/
  projective : ∀ X, Projective (scheme.obj X).hom
  /-- The specified dimension is the geometric Krull dimension. -/
  dimension_eq : ∀ X,
    topologicalKrullDim (scheme.obj X).left = (dimension X : WithBot ℕ∞)
  /-- The specified binary product represents the fibre product over `Spec(k)`. -/
  schemeProduct : ∀ X Y, scheme.obj (product X Y) ≅ scheme.obj X ⨯ scheme.obj Y
  /-- The specified first projection is the geometric product projection. -/
  scheme_fst : ∀ X Y, scheme.map (fst X Y) =
    (schemeProduct X Y).hom ≫ Limits.prod.fst
  /-- The specified second projection is the geometric product projection. -/
  scheme_snd : ∀ X Y, scheme.map (snd X Y) =
    (schemeProduct X Y).hom ≫ Limits.prod.snd
  /-- The specified point represents `Spec(k)` over itself. -/
  schemePoint : scheme.obj point ≅ Over.mk (𝟙 (Spec (CommRingCat.of k)))
  /-- Every smooth projective variety over `k` is represented by an object of `V`. -/
  scheme_essentiallySurjective : ∀ (S : SchemeOverField k)
    [Variety S] [Smooth S.hom] [Projective S.hom],
    ∃ X : V, Nonempty (scheme.obj X ≅ S)
  /-- Chow pullback by an identity is the identity. -/
  cyclePullback_id : ∀ X,
    cyclePullback (𝟙 X) = GradedAlgHom.id ℤ (CHgrade X)
  /-- Chow pullback reverses composition. -/
  cyclePullback_comp : ∀ {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z),
    cyclePullback (f ≫ g) = (cyclePullback f).comp (cyclePullback g)
  /-- Chow pushforward by an identity is the identity. -/
  cyclePushforward_id : ∀ X,
    cyclePushforward (𝟙 X) = AddMonoidHom.id (CH X)
  /-- Chow pushforward preserves composition. -/
  cyclePushforward_comp : ∀ {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z),
    cyclePushforward (f ≫ g) = (cyclePushforward g).comp (cyclePushforward f)

namespace SmoothProjectiveContext

/-- Build a smooth-projective presentation from its geometric realization and
specified Chow-theoretic operations. -/
def ofGeometry
    {k : Type u} [Field k] {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    (scheme : V ⥤ SchemeOverField k) (scheme_fullyFaithful : scheme.FullyFaithful)
    (variety : ∀ X, Variety (scheme.obj X))
    (smooth : ∀ X, Smooth (scheme.obj X).hom)
    (projective : ∀ X, Projective (scheme.obj X).hom)
    (dimension_eq : ∀ X,
      topologicalKrullDim (scheme.obj X).left = (dimension X : WithBot ℕ∞))
    (schemeProduct : ∀ X Y, scheme.obj (product X Y) ≅ scheme.obj X ⨯ scheme.obj Y)
    (scheme_fst : ∀ X Y, scheme.map (fst X Y) =
      (schemeProduct X Y).hom ≫ Limits.prod.fst)
    (scheme_snd : ∀ X Y, scheme.map (snd X Y) =
      (schemeProduct X Y).hom ≫ Limits.prod.snd)
    (schemePoint : scheme.obj point ≅ Over.mk (𝟙 (Spec (CommRingCat.of k))))
    (scheme_essentiallySurjective : ∀ (S : SchemeOverField k)
      [Variety S] [Smooth S.hom] [Projective S.hom],
      ∃ X : V, Nonempty (scheme.obj X ≅ S))
    (cyclePullback_id : ∀ X,
      cyclePullback (𝟙 X) = GradedAlgHom.id ℤ (CHgrade X))
    (cyclePullback_comp : ∀ {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z),
      cyclePullback (f ≫ g) = (cyclePullback f).comp (cyclePullback g))
    (cyclePushforward_id : ∀ X,
      cyclePushforward (𝟙 X) = AddMonoidHom.id (CH X))
    (cyclePushforward_comp : ∀ {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z),
      cyclePushforward (f ≫ g) = (cyclePushforward g).comp (cyclePushforward f)) :
    SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle where
  scheme := scheme
  scheme_fullyFaithful := scheme_fullyFaithful
  variety := variety
  smooth := smooth
  projective := projective
  dimension_eq := dimension_eq
  schemeProduct := schemeProduct
  scheme_fst := scheme_fst
  scheme_snd := scheme_snd
  schemePoint := schemePoint
  scheme_essentiallySurjective := scheme_essentiallySurjective
  cyclePullback_id := cyclePullback_id
  cyclePullback_comp := cyclePullback_comp
  cyclePushforward_id := cyclePushforward_id
  cyclePushforward_comp := cyclePushforward_comp

/-- The distinguished point in a smooth-projective presentation has dimension zero. -/
theorem point_dimension
    {k : Type u} [Field k] {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    (G : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle) :
    dimension point = 0 := sorry

/-- The Chow motive of a scheme represented by a smooth-projective context. -/
public noncomputable def motive
    {k : Type u} [Field k] {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    (C : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle) (X : V) :
    ChowMotive k (fun _ ↦ AlgebraicGeometry.Correspondence.GradedCategory k) :=
  @ChowMotive.h k _ (C.scheme.obj X) (C.smooth X) (C.projective X)

/-- The scheme underlying the motive represented by `X` is `C.scheme.obj X`. -/
public theorem motive_scheme
    {k : Type u} [Field k] {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    (C : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle) (X : V) :
    (C.motive X).X.1.scheme = C.scheme.obj X := sorry

end SmoothProjectiveContext

end WeilCohomology
