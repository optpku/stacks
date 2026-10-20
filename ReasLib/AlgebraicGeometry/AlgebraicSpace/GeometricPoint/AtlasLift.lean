/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.SmallEtaleFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AtlasCharts
public import Mathlib.AlgebraicGeometry.Sites.Etale

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint
variable {S : Scheme.{u}}

/-- A geometric point lifted to the scheme atlas by splitting an étale covering of its
algebraically closed source spectrum. -/
def atlasLiftHom {X : AlgebraicSpace S} (xbar : GeometricPoint X) :
    Over.mk xbar.structureHom ⟶ SmallEtale.AtlasCharts.atlasOver X := by
  let a := SmallEtale.AtlasCharts.atlasMap X
  let s : X.functorOfPoints.obj (op xbar.overObj) := yonedaEquiv xbar.hom
  let R := Presheaf.imageSieve a s
  have hR : R ∈ (Scheme.etaleTopology.over S) xbar.overObj :=
    (SmallEtale.AtlasCharts.atlasMap_surjective X).imageSieve_mem s
  have hR' : Sieve.overEquiv xbar.overObj R ∈ Scheme.etaleTopology xbar.overObj.left :=
    (GrothendieckTopology.mem_over_iff _ R).mp hR
  let point := @Scheme.geometricFiber xbar.K xbar.field
    (@IsSepClosed.of_isAlgClosed xbar.K xbar.field xbar.isAlgClosed)
  have lift := point.jointly_surjective _ hR' (𝟙 _)
  let T := lift.choose
  let g := lift.choose_spec.choose
  have hg := lift.choose_spec.choose_spec.choose
  let t := lift.choose_spec.choose_spec.choose_spec.choose
  have ht := lift.choose_spec.choose_spec.choose_spec.choose_spec
  let gOver : Over.mk (g ≫ xbar.structureHom) ⟶ xbar.overObj := Over.homMk g
  have hgOver : R gOver := by
    have h := congrArg (fun Q : Sieve xbar.overObj ↦ Q gOver)
      (Sieve.functorPullback_functorPushforward_overForget R)
    exact h.mp hg
  change Presheaf.imageSieve a s gOver at hgOver
  let z : Over.mk (g ≫ xbar.structureHom) ⟶ SmallEtale.AtlasCharts.atlasOver X :=
    Presheaf.localPreimage a (U := op xbar.overObj) s gOver hgOver
  change Spec (.of xbar.K) ⟶ T at t
  change t ≫ g = 𝟙 (Spec (.of xbar.K)) at ht
  let l : Over.mk xbar.structureHom ⟶ Over.mk (g ≫ xbar.structureHom) :=
    Over.homMk t sorry
  exact l ≫ z

/-- The atlas lift lies over the given geometric point. -/
theorem atlasLiftHom_fac {X : AlgebraicSpace S} (xbar : GeometricPoint X) :
    ofOverMap (atlasLiftHom xbar) ≫ (SmallEtale.AtlasCharts.atlasObject X).hom = xbar.hom := by
  unfold atlasLiftHom
  extract_lets a s R hR hR' point lift T g hg t ht gOver hgOver l
  change ofOverMap
    (l ≫ Presheaf.localPreimage a (U := op xbar.overObj) s gOver hgOver) ≫ a = xbar.hom
  have hlg : l ≫ gOver = 𝟙 xbar.overObj := by
    apply Over.OverMorphism.ext
    exact ht
  change yoneda.map
    (l ≫ Presheaf.localPreimage a (U := op xbar.overObj) s gOver hgOver) ≫ a = xbar.hom
  apply yonedaEquiv.injective
  rw [Functor.map_comp, Category.assoc, ← yonedaEquiv_naturality,
    yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  refine (congrArg (fun v ↦ X.functorOfPoints.map l.op v)
    (Presheaf.app_localPreimage a (U := op xbar.overObj) s gOver hgOver)).trans ?_
  rw [← Functor.map_comp_apply, ← op_comp, hlg]
  exact X.functorOfPoints.map_id_apply _ s

/-- The supplied scheme atlas admits a lift of every geometric point. -/
theorem exists_atlasLiftHom {X : AlgebraicSpace S} (xbar : GeometricPoint X) :
    ∃ l : Over.mk xbar.structureHom ⟶ SmallEtale.AtlasCharts.atlasOver X,
      ofOverMap l ≫ (SmallEtale.AtlasCharts.atlasObject X).hom = xbar.hom :=
  ⟨atlasLiftHom xbar, atlasLiftHom_fac xbar⟩

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint

namespace AlgebraicGeometry.AlgebraicSpace

/-- A lift of a geometric point through the supplied scheme atlas, with its commuting
triangle over the algebraic space. -/
def atlasLift {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X) :
    GeometricPoint.OverLift xbar (SmallEtale.AtlasCharts.atlasObject X) :=
  ⟨GeometricPoint.atlasLiftHom xbar, GeometricPoint.atlasLiftHom_fac xbar⟩

end AlgebraicGeometry.AlgebraicSpace
