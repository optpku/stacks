/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ConstantGroup

/-!
# Points of the constant group algebraic space

Scheme-valued points of `G_B` over a morphism `t : ofOver T ⟶ B` are locally constant maps
`T → G`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization
open scoped AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
open CartesianMonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.ConstantGroup

-- This comparison unfolds the two chosen Cartesian monoidal structures.
set_option maxHeartbeats 800000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Morphisms over `B` from a scheme `T` to the constant group algebraic space `G_B` are
locally constant maps `T → G`. -/
def homMulEquiv {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GrpCat.{u})
    (T : Over S) (t : ofOver T ⟶ B) :
    (Over.mk t ⟶ (space B G).X) ≃* LocallyConstant T.left G where
  toFun f :=
    baseChangeHomMulEquiv S G T
      (Yoneda.fullyFaithful.homEquiv.symm
        (((Over.mapPullbackAdj (toBase B)).homEquiv (Over.mk t)
            (Over.mk (toBase (ofOver (baseChange S G).X)))).symm f).left)
  invFun a :=
    ((Over.mapPullbackAdj (toBase B)).homEquiv (Over.mk t)
        (Over.mk (toBase (ofOver (baseChange S G).X))))
      (Over.homMk (Yoneda.fullyFaithful.homEquiv ((baseChangeHomMulEquiv S G T).symm a))
        (by rfl))
  left_inv := by
    intro f
    apply ((Over.mapPullbackAdj (toBase B)).homEquiv (Over.mk t)
      (Over.mk (toBase (ofOver (baseChange S G).X)))).symm.injective
    apply Over.OverMorphism.ext
    simp
  right_inv := by
    intro a
    simp
  map_mul' := by
    intro f g
    let U := (baseChange S G).X
    let A := Over.mk (toBase (ofOver U))
    let e := (Over.mapPullbackAdj (toBase B)).homEquiv (Over.mk t) A
    have hAdj (f g : Over.mk t ⟶ (space B G).X) :
        e.symm (f * g) = e.symm f * e.symm g := by
      change Over.mk t ⟶ (Over.pullback (toBase B)).obj A at f g
      apply Over.OverMorphism.ext
      change (lift f g).left ≫
        (Functor.LaxMonoidal.μ (Over.pullback (toBase B)) A A).left ≫
        ((Over.pullback (toBase B)).map μ[A]).left ≫
        pullback.fst A.hom (toBase B) =
          (lift (e.symm f) (e.symm g)).left ≫ (μ[A]).left
      have hMap : ((Over.pullback (toBase B)).map μ[A]).left ≫
          pullback.fst A.hom (toBase B) =
            pullback.fst (A ⊗ A).hom (toBase B) ≫ (μ[A]).left :=
        pullback.lift_fst _ _ _
      have hPair : (lift f g).left ≫
          (Functor.LaxMonoidal.μ (Over.pullback (toBase B)) A A).left ≫
          pullback.fst (A ⊗ A).hom (toBase B) =
            (lift (e.symm f) (e.symm g)).left := by
        apply Over.tensorObj_ext
        · calc
            _ = (lift f g).left ≫
                ((Functor.LaxMonoidal.μ (Over.pullback (toBase B)) A A).left ≫
                  pullback.fst (A ⊗ A).hom (toBase B) ≫ pullback.fst A.hom A.hom) := rfl
            _ = (lift f g).left ≫
                (pullback.fst _ _ ≫ pullback.fst A.hom (toBase B)) :=
              congrArg (fun l ↦ (lift f g).left ≫ l) (Over.μ_pullback_left_fst_fst A A)
            _ = f.left ≫ pullback.fst A.hom (toBase B) :=
              congrArg (fun l : Over.mk t ⟶ (Over.pullback (toBase B)).obj A ↦
                l.left ≫ pullback.fst A.hom (toBase B)) (lift_fst f g)
            _ = _ := (congrArg
              (fun l : (Over.map (toBase B)).obj (Over.mk t) ⟶ A ↦ l.left)
              (lift_fst (e.symm f) (e.symm g))).symm
        · calc
            _ = (lift f g).left ≫
                ((Functor.LaxMonoidal.μ (Over.pullback (toBase B)) A A).left ≫
                  pullback.fst (A ⊗ A).hom (toBase B) ≫ pullback.snd A.hom A.hom) := rfl
            _ = (lift f g).left ≫
                (pullback.snd _ _ ≫ pullback.fst A.hom (toBase B)) :=
              congrArg (fun l ↦ (lift f g).left ≫ l) (Over.μ_pullback_left_fst_snd A A)
            _ = g.left ≫ pullback.fst A.hom (toBase B) :=
              congrArg (fun l : Over.mk t ⟶ (Over.pullback (toBase B)).obj A ↦
                l.left ≫ pullback.fst A.hom (toBase B)) (lift_snd f g)
            _ = _ := (congrArg
              (fun l : (Over.map (toBase B)).obj (Over.mk t) ⟶ A ↦ l.left)
              (lift_snd (e.symm f) (e.symm g))).symm
      calc
        _ = ((lift f g).left ≫
            (Functor.LaxMonoidal.μ (Over.pullback (toBase B)) A A).left ≫
            pullback.fst (A ⊗ A).hom (toBase B)) ≫ (μ[A]).left :=
          congrArg (fun l : ((Over.pullback (toBase B)).obj (A ⊗ A)).left ⟶ A.left ↦
            (lift f g).left ≫
              (Functor.LaxMonoidal.μ (Over.pullback (toBase B)) A A).left ≫ l) hMap
        _ = (lift (e.symm f) (e.symm g)).left ≫ (μ[A]).left :=
          congrArg (fun l : (Over.mk t).left ⟶ (A ⊗ A).left ↦ l ≫ (μ[A]).left) hPair
    have hYoneda (a b : (Over.map (toBase B)).obj (Over.mk t) ⟶ A) :
        Yoneda.fullyFaithful.homEquiv.symm (a * b).left =
          Yoneda.fullyFaithful.homEquiv.symm a.left *
            Yoneda.fullyFaithful.homEquiv.symm b.left := by
      let pa : T ⟶ U := Yoneda.fullyFaithful.homEquiv.symm a.left
      let pb : T ⟶ U := Yoneda.fullyFaithful.homEquiv.symm b.left
      let c : ofOver T ⟶ ofOverPullback U U :=
        (lift a b).left ≫ ofOverPullbackHom U U
      have hcfst : c ≫ ofOverPullbackFst U U = a.left := by
        simp only [c, ofOverPullbackHom, ofOverPullbackFst, Category.assoc,
          ReasLibPullback.pullbackLift_fst, Over.lift_left]
        exact pullback.lift_fst _ _ _
      have hcsnd : c ≫ ofOverPullbackSnd U U = b.left := by
        simp only [c, ofOverPullbackHom, ofOverPullbackSnd, Category.assoc,
          ReasLibPullback.pullbackLift_snd, Over.lift_left]
        exact pullback.lift_snd _ _ _
      have ha : ofOverPoint ((ofOverPullbackFst U U).app (op T)
          (c.app (op T) (𝟙 T))) = pa := by
        change (𝟙 T) ≫ ((ofOverPullbackFst U U).app (op T)
          (c.app (op T) (𝟙 T))) = pa
        rw [Category.id_comp]
        exact congrArg (fun h : ofOver T ⟶ ofOver U ↦ h.app (op T) (𝟙 T)) hcfst
      have hb : ofOverPoint ((ofOverPullbackSnd U U).app (op T)
          (c.app (op T) (𝟙 T))) = pb := by
        change (𝟙 T) ≫ ((ofOverPullbackSnd U U).app (op T)
          (c.app (op T) (𝟙 T))) = pb
        rw [Category.id_comp]
        exact congrArg (fun h : ofOver T ⟶ ofOver U ↦ h.app (op T) (𝟙 T)) hcsnd
      change ((tensorComparison U U).app (op T) (c.app (op T) (𝟙 T))) ≫ μ[U] =
        lift pa pb ≫ μ[U]
      congr 1
      change (𝟙 T) ≫ lift
          (ofOverPoint ((ofOverPullbackFst U U).app (op T) (c.app (op T) (𝟙 T))))
          (ofOverPoint ((ofOverPullbackSnd U U).app (op T) (c.app (op T) (𝟙 T)))) =
        lift pa pb
      rw [Category.id_comp, ha, hb]
    change baseChangeHomMulEquiv S G T
        (Yoneda.fullyFaithful.homEquiv.symm (e.symm (f * g)).left) =
      baseChangeHomMulEquiv S G T (Yoneda.fullyFaithful.homEquiv.symm (e.symm f).left) *
        baseChangeHomMulEquiv S G T (Yoneda.fullyFaithful.homEquiv.symm (e.symm g).left)
    exact (congrArg
      (fun l : (Over.map (toBase B)).obj (Over.mk t) ⟶ A ↦
        baseChangeHomMulEquiv S G T (Yoneda.fullyFaithful.homEquiv.symm l.left))
      (hAdj f g)).trans
        ((congrArg (baseChangeHomMulEquiv S G T) (hYoneda (e.symm f) (e.symm g))).trans
          (map_mul (baseChangeHomMulEquiv S G T) _ _))

/-- The forward map of `homMulEquiv` is the composite of the pullback adjunction, Yoneda, and
`baseChangeHomMulEquiv`. -/
theorem homMulEquiv_apply {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GrpCat.{u})
    (T : Over S) (t : ofOver T ⟶ B) (f : Over.mk t ⟶ (space B G).X) :
    homMulEquiv G T t f =
      baseChangeHomMulEquiv S G T
        (Yoneda.fullyFaithful.homEquiv.symm
          (((Over.mapPullbackAdj (toBase B)).homEquiv (Over.mk t)
              (Over.mk (toBase (ofOver (baseChange S G).X)))).symm f).left) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition of points over `B` corresponds to precomposition of locally constant maps. -/
theorem homMulEquiv_naturality {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GrpCat.{u})
    (T T' : Over S) (baseMap : ofOver T ⟶ B) (baseMap' : ofOver T' ⟶ B)
    (testMap : T' ⟶ T) (h_over : SchemeRealization.ofOverMap testMap ≫ baseMap = baseMap')
    (point : Over.mk baseMap ⟶ (space B G).X) :
    homMulEquiv G T' baseMap'
        (Over.homMk (V := Over.mk baseMap) (SchemeRealization.ofOverMap testMap) h_over ≫ point) =
      pointsMap G testMap (homMulEquiv G T baseMap point) := by
  let A := Over.mk (toBase (ofOver (baseChange S G).X))
  let adj := Over.mapPullbackAdj (toBase B)
  let k : Over.mk baseMap' ⟶ Over.mk baseMap := Over.homMk (ofOverMap testMap) h_over
  let q := (adj.homEquiv (Over.mk baseMap) A).symm point
  let p : T ⟶ (baseChange S G).X := Yoneda.fullyFaithful.homEquiv.symm q.left
  have hp : Yoneda.fullyFaithful.homEquiv.symm
        ((adj.homEquiv (Over.mk baseMap') A).symm (k ≫ point)).left = testMap ≫ p := by
    have hc := congrArg
      (fun l : (Over.map (toBase B)).obj (Over.mk baseMap') ⟶ A ↦
        Yoneda.fullyFaithful.homEquiv.symm l.left)
      (adj.homEquiv_naturality_left_symm k point)
    refine hc.trans ?_
    exact (Yoneda.fullyFaithful.preimage_comp (yoneda.map testMap)
      (q.left : yoneda.obj T ⟶ yoneda.obj (baseChange S G).X)).trans
        (congrArg (fun l ↦ l ≫ p) (Yoneda.fullyFaithful.preimage_map testMap))
  have hn := congrArg (fun l ↦ l p)
    (baseChangeComponentIso_naturality S G testMap.op)
  change baseChangeHomMulEquiv S G T' (testMap ≫ p) =
    pointsMap G testMap (baseChangeHomMulEquiv S G T p) at hn
  exact (congrArg (baseChangeHomMulEquiv S G T') hp).trans hn

/-- The Type `u` fibre of morphisms over `B` from a scheme `T` into `space B G`. -/
def pointsFibre {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GrpCat.{u})
    (T : Over S) (t : ofOver T ⟶ B) : Type u :=
  { s : (space B G).X.left.functorOfPoints.obj (op T) //
    (space B G).X.hom.app (op T) s = yonedaEquiv t }

/-- The comparison from the fibre of `T`-points over `t` to morphisms over `B`. -/
def pointsFibreHomEquiv {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GrpCat.{u})
    (T : Over S) (t : ofOver T ⟶ B) :
    pointsFibre G T t ≃ (Over.mk t ⟶ (space B G).X) where
  toFun s := Over.homMk (yonedaEquiv.symm s.1) (by
    exact (yonedaEquiv_symm_naturality_right T (space B G).X.hom s.1).trans
      ((congrArg yonedaEquiv.symm s.2).trans (yonedaEquiv.symm_apply_apply t)))
  invFun f := ⟨yonedaEquiv f.left, by
    exact (yonedaEquiv_comp f.left (space B G).X.hom).symm.trans
      (congrArg (fun k : ofOver T ⟶ B ↦ yonedaEquiv k) (Over.w f))⟩
  left_inv := by
    intro s
    apply Subtype.ext
    exact yonedaEquiv.apply_symm_apply s.1
  right_inv := by
    intro f
    apply Over.OverMorphism.ext
    exact yonedaEquiv.symm_apply_apply f.left

/-- Scheme-valued points of `G_B` over `t` in Type `u` are locally constant maps `T → G`. -/
def pointsFibreEquiv {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GrpCat.{u})
    (T : Over S) (t : ofOver T ⟶ B) :
    pointsFibre G T t ≃ LocallyConstant T.left G :=
  (pointsFibreHomEquiv G T t).trans (homMulEquiv G T t).toEquiv

/-- The forward map of `pointsFibreEquiv` is the composite of `pointsFibreHomEquiv` with
`homMulEquiv`. -/
theorem pointsFibreEquiv_apply {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GrpCat.{u})
    (T : Over S) (t : ofOver T ⟶ B) (s : pointsFibre G T t) :
    pointsFibreEquiv G T t s = homMulEquiv G T t (pointsFibreHomEquiv G T t s) :=
  rfl

end AlgebraicGeometry.ConstantGroup
