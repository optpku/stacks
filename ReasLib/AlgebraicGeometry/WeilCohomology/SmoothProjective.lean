/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Properties
public import ReasLib.AlgebraicGeometry.ChowMotive.Duality
public import ReasLib.AlgebraicGeometry.ChowCohomology.Restriction
public import ReasLib.AlgebraicGeometry.ChowGroup.TotalFundamental

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators DirectSum

universe u w y z

namespace WeilCohomology

namespace SmoothProjectiveChow

/-- Cap a homogeneous operational class with every dimensional component of the
fundamental class. The finite sum also applies to disconnected and empty schemes. -/
noncomputable def capDegree {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom]
    [CompactSpace X.left] (i : ℤ) :
    ChowCohomology.degree δ X.hom i →+ ChowGroup.Total δ X where
  toFun c := ∑ n ∈ ChowGroup.relativeDimensionDegrees δ X,
    DirectSum.of _ (n - i)
      (c.cap (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom))
        IsPullback.of_id_snd n (RelativeChow.fundamentalClass δ (Over.mk X.hom) n))
  map_zero' := by sorry
  map_add' := by sorry

/-- The actual map `c ↦ c ∩ [X]`, extended additively over all codimensions. -/
noncomputable def capFundamental {k : Type u} [Field k]
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] :
    ChowCohomology.ring (fun _ ↦ 0) X.hom →+
      ChowGroup.Total (fun _ ↦ 0) X := by
  letI : CompactSpace (Spec (CommRingCat.of k)) := Scheme.compactSpace_of_isAffine _
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  exact DirectSum.toAddMonoid (capDegree (fun _ ↦ 0) X)

/-- Smooth Chow duality, applied separately to the open and closed dimension strata.
This is a proposition, not a chosen inverse used in a data definition. -/
theorem capFundamental_bijective {k : Type u} [Field k]
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] :
    Function.Bijective (capFundamental X) := sorry

/-- Under cap with the fundamental class, the operational unit is `[X]`. -/
theorem capFundamental_one {k : Type u} [Field k]
    (X : SchemeOverField k) [Smooth X.hom] [Projective X.hom] :
    letI : CompactSpace (Spec (CommRingCat.of k)) := Scheme.compactSpace_of_isAffine _
    letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
    capFundamental X 1 = ChowGroup.totalFundamentalClass (fun _ ↦ 0) X := sorry

/-- Actual proper pushforward on total Chow homology. A morphism between
projective schemes is proper because its target is separated over the base. -/
noncomputable def pushforward {k : Type u} [Field k]
    {X Y : SchemeOverField k} [Smooth X.hom] [Smooth Y.hom]
    [Projective X.hom] [Projective Y.hom] (f : X ⟶ Y) :
    ChowGroup.Total (fun _ ↦ 0) X →+ ChowGroup.Total (fun _ ↦ 0) Y := by
  letI : IsProper (f.left ≫ Y.hom) := by
    simpa using (inferInstance : IsProper X.hom)
  letI : IsProper f.left := IsProper.of_comp f.left Y.hom
  exact ChowGroup.Total.map (fun _ ↦ 0) f

end SmoothProjectiveChow

/-- A presentation of all smooth projective schemes over an arbitrary field `k`,
including the empty scheme and finite disjoint unions. The supplied graded Chow
rings and operations are identified with those of the represented schemes. -/
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
  /-- Every represented scheme is smooth over `k`. -/
  smooth : ∀ X, Smooth (scheme.obj X).hom
  /-- Every represented scheme is projective over `k`. -/
  projective : ∀ X, Projective (scheme.obj X).hom
  /-- For nonempty schemes the specified dimension is the geometric Krull dimension. -/
  dimension_eq : ∀ X, Nonempty (scheme.obj X).left →
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
  /-- Every smooth projective scheme over `k` is represented by an object of `V`. -/
  scheme_essentiallySurjective : ∀ (S : SchemeOverField k)
    [Smooth S.hom] [Projective S.hom],
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

  /-- The specified Chow ring is a presentation of the actual operational Chow ring. -/
  chowEquiv : ∀ X, letI := smooth X
    CH X ≃ₐ[ℤ] ChowCohomology.ring (fun _ ↦ 0) (scheme.obj X).hom
  /-- The specified grading is the actual codimension grading. -/
  chowGrade_eq : ∀ X (i : ℤ), letI := smooth X
    CHgrade X i = (LinearMap.range (DirectSum.lof ℤ ℤ
      (ChowCohomology.degree (fun _ ↦ 0) (scheme.obj X).hom) i)).comap
        (chowEquiv X).toLinearMap
  /-- Chow pullback is canonical operational restriction, also for nonflat maps. -/
  chowPullback_eq : ∀ {X Y : V} (f : X ⟶ Y) (a : CH Y),
    letI := smooth X
    letI := smooth Y
    chowEquiv X (cyclePullback f a) =
      ChowCohomology.restrict (fun _ ↦ 0) (scheme.map f) (chowEquiv Y a)
  /-- Chow pushforward agrees, under cap with `[X]`, with actual proper pushforward.
  Cap is bijective for smooth schemes, so this determines the supplied map. -/
  chowPushforward_eq : ∀ {X Y : V} (f : X ⟶ Y) (a : CH X),
    letI := smooth X
    letI := smooth Y
    letI := projective X
    letI := projective Y
    SmoothProjectiveChow.capFundamental (scheme.obj Y) (chowEquiv Y (cyclePushforward f a)) =
      SmoothProjectiveChow.pushforward (scheme.map f)
        (SmoothProjectiveChow.capFundamental (scheme.obj X) (chowEquiv X a))
  /-- The point cycle is the operational unit, hence caps to the fundamental class. -/
  pointCycle_eq : letI := smooth point
    chowEquiv point (pointCycle : CH point) = 1

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
    (smooth : ∀ X, Smooth (scheme.obj X).hom)
    (projective : ∀ X, Projective (scheme.obj X).hom)
    (dimension_eq : ∀ X, Nonempty (scheme.obj X).left →
      topologicalKrullDim (scheme.obj X).left = (dimension X : WithBot ℕ∞))
    (schemeProduct : ∀ X Y, scheme.obj (product X Y) ≅ scheme.obj X ⨯ scheme.obj Y)
    (scheme_fst : ∀ X Y, scheme.map (fst X Y) =
      (schemeProduct X Y).hom ≫ Limits.prod.fst)
    (scheme_snd : ∀ X Y, scheme.map (snd X Y) =
      (schemeProduct X Y).hom ≫ Limits.prod.snd)
    (schemePoint : scheme.obj point ≅ Over.mk (𝟙 (Spec (CommRingCat.of k))))
    (scheme_essentiallySurjective : ∀ (S : SchemeOverField k)
      [Smooth S.hom] [Projective S.hom],
      ∃ X : V, Nonempty (scheme.obj X ≅ S))
    (cyclePullback_id : ∀ X,
      cyclePullback (𝟙 X) = GradedAlgHom.id ℤ (CHgrade X))
    (cyclePullback_comp : ∀ {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z),
      cyclePullback (f ≫ g) = (cyclePullback f).comp (cyclePullback g))
    (cyclePushforward_id : ∀ X,
      cyclePushforward (𝟙 X) = AddMonoidHom.id (CH X))
    (cyclePushforward_comp : ∀ {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z),
      cyclePushforward (f ≫ g) = (cyclePushforward g).comp (cyclePushforward f))
    (chowEquiv : ∀ X, letI := smooth X
      CH X ≃ₐ[ℤ] ChowCohomology.ring (fun _ ↦ 0) (scheme.obj X).hom)
    (chowGrade_eq : ∀ X (i : ℤ), letI := smooth X
      CHgrade X i = (LinearMap.range (DirectSum.lof ℤ ℤ
        (ChowCohomology.degree (fun _ ↦ 0) (scheme.obj X).hom) i)).comap
          (chowEquiv X).toLinearMap)
    (chowPullback_eq : ∀ {X Y : V} (f : X ⟶ Y) (a : CH Y),
      letI := smooth X
      letI := smooth Y
      chowEquiv X (cyclePullback f a) =
        ChowCohomology.restrict (fun _ ↦ 0) (scheme.map f) (chowEquiv Y a))
    (chowPushforward_eq : ∀ {X Y : V} (f : X ⟶ Y) (a : CH X),
      letI := smooth X
      letI := smooth Y
      letI := projective X
      letI := projective Y
      SmoothProjectiveChow.capFundamental (scheme.obj Y) (chowEquiv Y (cyclePushforward f a)) =
        SmoothProjectiveChow.pushforward (scheme.map f)
          (SmoothProjectiveChow.capFundamental (scheme.obj X) (chowEquiv X a)))
    (pointCycle_eq : letI := smooth point
      chowEquiv point (pointCycle : CH point) = 1) :
    SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle where
  scheme := scheme
  scheme_fullyFaithful := scheme_fullyFaithful
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
  chowEquiv := chowEquiv
  chowGrade_eq := chowGrade_eq
  chowPullback_eq := chowPullback_eq
  chowPushforward_eq := chowPushforward_eq
  pointCycle_eq := pointCycle_eq

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

/-- The domain of classical Weil cohomology (Stacks, Section 45.7): smooth
projective integral varieties over an algebraically closed field. Over this base
products remain integral. This is independent of the context of all schemes. -/
structure SmoothProjectiveVarietyContext
    (k : Type u) [Field k] [IsAlgClosed k] (V : Type w) [Category.{z} V]
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
  /-- Every represented object is an integral variety over `k`. -/
  variety : ∀ X, Variety (scheme.obj X)
  /-- Every represented variety is smooth over `k`. -/
  smooth : ∀ X, Smooth (scheme.obj X).hom
  /-- Every represented scheme is projective over `k`. -/
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

  /-- The specified Chow ring is a presentation of the actual operational Chow ring. -/
  chowEquiv : ∀ X, letI := smooth X
    CH X ≃ₐ[ℤ] ChowCohomology.ring (fun _ ↦ 0) (scheme.obj X).hom
  /-- The specified grading is the actual codimension grading. -/
  chowGrade_eq : ∀ X (i : ℤ), letI := smooth X
    CHgrade X i = (LinearMap.range (DirectSum.lof ℤ ℤ
      (ChowCohomology.degree (fun _ ↦ 0) (scheme.obj X).hom) i)).comap
        (chowEquiv X).toLinearMap
  /-- Chow pullback is canonical operational restriction, also for nonflat maps. -/
  chowPullback_eq : ∀ {X Y : V} (f : X ⟶ Y) (a : CH Y),
    letI := smooth X
    letI := smooth Y
    chowEquiv X (cyclePullback f a) =
      ChowCohomology.restrict (fun _ ↦ 0) (scheme.map f) (chowEquiv Y a)
  /-- Chow pushforward agrees, under cap with `[X]`, with actual proper pushforward.
  Cap is bijective for smooth schemes, so this determines the supplied map. -/
  chowPushforward_eq : ∀ {X Y : V} (f : X ⟶ Y) (a : CH X),
    letI := smooth X
    letI := smooth Y
    letI := projective X
    letI := projective Y
    SmoothProjectiveChow.capFundamental (scheme.obj Y) (chowEquiv Y (cyclePushforward f a)) =
      SmoothProjectiveChow.pushforward (scheme.map f)
        (SmoothProjectiveChow.capFundamental (scheme.obj X) (chowEquiv X a))
  /-- The point cycle is the operational unit, hence caps to the fundamental class. -/
  pointCycle_eq : letI := smooth point
    chowEquiv point (pointCycle : CH point) = 1

namespace SmoothProjectiveVarietyContext

/-- Build a smooth-projective presentation from its geometric realization and
specified Chow-theoretic operations. -/
def ofGeometry
    {k : Type u} [Field k] [IsAlgClosed k] {V : Type w} [Category.{z} V]
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
    (dimension_eq : ∀ X, topologicalKrullDim (scheme.obj X).left = (dimension X : WithBot ℕ∞))
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
      cyclePushforward (f ≫ g) = (cyclePushforward g).comp (cyclePushforward f))
    (chowEquiv : ∀ X, letI := smooth X
      CH X ≃ₐ[ℤ] ChowCohomology.ring (fun _ ↦ 0) (scheme.obj X).hom)
    (chowGrade_eq : ∀ X (i : ℤ), letI := smooth X
      CHgrade X i = (LinearMap.range (DirectSum.lof ℤ ℤ
        (ChowCohomology.degree (fun _ ↦ 0) (scheme.obj X).hom) i)).comap
          (chowEquiv X).toLinearMap)
    (chowPullback_eq : ∀ {X Y : V} (f : X ⟶ Y) (a : CH Y),
      letI := smooth X
      letI := smooth Y
      chowEquiv X (cyclePullback f a) =
        ChowCohomology.restrict (fun _ ↦ 0) (scheme.map f) (chowEquiv Y a))
    (chowPushforward_eq : ∀ {X Y : V} (f : X ⟶ Y) (a : CH X),
      letI := smooth X
      letI := smooth Y
      letI := projective X
      letI := projective Y
      SmoothProjectiveChow.capFundamental (scheme.obj Y) (chowEquiv Y (cyclePushforward f a)) =
        SmoothProjectiveChow.pushforward (scheme.map f)
          (SmoothProjectiveChow.capFundamental (scheme.obj X) (chowEquiv X a)))
    (pointCycle_eq : letI := smooth point
      chowEquiv point (pointCycle : CH point) = 1) :
    SmoothProjectiveVarietyContext k V dimension product fst snd point CH CHgrade
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
  chowEquiv := chowEquiv
  chowGrade_eq := chowGrade_eq
  chowPullback_eq := chowPullback_eq
  chowPushforward_eq := chowPushforward_eq
  pointCycle_eq := pointCycle_eq

/-- The distinguished point in a smooth-projective presentation has dimension zero. -/
theorem point_dimension
    {k : Type u} [Field k] [IsAlgClosed k] {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    (G : SmoothProjectiveVarietyContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle) :
    dimension point = 0 := sorry

/-- The Chow motive of a scheme represented by a smooth-projective context. -/
public noncomputable def motive
    {k : Type u} [Field k] [IsAlgClosed k] {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    (C : SmoothProjectiveVarietyContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle) (X : V) :
    ChowMotive k (fun _ ↦ AlgebraicGeometry.Correspondence.GradedCategory k) :=
  @ChowMotive.h k _ (C.scheme.obj X) (C.smooth X) (C.projective X)

/-- The scheme underlying the motive represented by `X` is `C.scheme.obj X`. -/
public theorem motive_scheme
    {k : Type u} [Field k] [IsAlgClosed k] {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    (C : SmoothProjectiveVarietyContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle) (X : V) :
    (C.motive X).X.1.scheme = C.scheme.obj X := sorry

end SmoothProjectiveVarietyContext

end WeilCohomology
