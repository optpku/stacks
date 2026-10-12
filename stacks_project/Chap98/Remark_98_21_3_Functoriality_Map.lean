/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.Remark_98_21_3_Functoriality_Pullback

/-!
# Induced Inf and tangent maps along a change of rings

An `S`-algebra map `A ⟶ B`, a fibre morphism `φ : x|_Spec(B) ⟶ y`, and an
`A`-linear map `M ⟶ N` induce `A`-linear maps `Inf_x(M) ⟶ Inf_y(N)` and
`T_x(M) ⟶ T_y(N)`. These are natural for the comparison isomorphism
`Inf_x(I) ≅ Inf(x'/x)` and for the action of `T_x(I)` on lifts.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Push an infinitesimal automorphism of the trivial deformation of `x` along
`A[M] ⟶ B[N]`. -/
def infTypeRestrict {S : Scheme.{u}} {X : GroupoidsOver S}
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y)
    (α : infType x M) : infType y N :=
  let e := (trivialDeformationRestrictIso v hv f x y φ).symm
  ⟨{ hom := e.hom ≫ Chosen.reindexMap X.p (specOverMapRestrict v hv f) α.1.hom ≫ e.inv
     inv := e.hom ≫ Chosen.reindexMap X.p (specOverMapRestrict v hv f) α.1.inv ≫ e.inv
     hom_inv_id := sorry
     inv_hom_id := sorry }, sorry⟩

/-- The canonical `A`-linear map `Inf_x(M) ⟶ Inf_y(N)` induced by `A ⟶ B` and an
`A`-linear map `M ⟶ N`. -/
def infMap {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y) :
    (infFunctor x).obj M ⟶
      (ModuleCat.restrictScalars v.hom).obj ((infFunctor y).obj N) :=
  ConcreteCategory.ofHom
    { toFun := infTypeRestrict v hv f x y φ
      map_add' := sorry
      map_smul' := sorry }

/-- `infMap` acts by `infTypeRestrict` on infinitesimal automorphisms of the
trivial deformation. -/
theorem infMap_apply {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y)
    (α : (infFunctor x).obj M) :
    infMap v hv f x y φ α = infTypeRestrict v hv f x y φ α := sorry

/-- The canonical `A`-linear map `T_x(M) ⟶ T_y(N)` induced by `A ⟶ B` and an
`A`-linear map `M ⟶ N`. -/
def tangentMap {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y) :
    (tangentFunctor x).obj M ⟶
      (ModuleCat.restrictScalars.{u + 1} v.hom).obj ((tangentFunctor y).obj N) :=
  ConcreteCategory.ofHom
    { toFun t :=
        (tangentForget y N).symm
          (liftsMap (trivSqZeroLiftPullback v hv f x y φ) (tangentForget x M t))
      map_add' := sorry
      map_smul' := sorry }

/-- `tangentMap` is `liftsMap` of the trivial-square-zero pullback after
identifying `T_x(M)` with `Lift(x, A[M])`. -/
theorem tangentMap_apply {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y)
    (t : (tangentFunctor x).obj M) :
    tangentMap v hv f x y φ t =
      (tangentForget y N).symm
        (liftsMap (trivSqZeroLiftPullback v hv f x y φ) (tangentForget x M t)) :=
  sorry

/-- Forgetting `T` after `tangentMap` is `liftsMap` of the trivial-square-zero
pullback. -/
theorem tangentForget_tangentMap {S : Scheme.{u}} {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X]
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars v.hom).obj N)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y)
    (t : (tangentFunctor x).obj M) :
    tangentForget y N (tangentMap v hv f x y φ t) =
      liftsMap (trivSqZeroLiftPullback v hv f x y φ) (tangentForget x M t) :=
  sorry

/-- Naturality of `Inf_x(I) ≅ Inf(x'/x)` in a morphism of deformation
situations. Here `y'` is the pullback of the given lift `x'`. -/
theorem infIso_natural {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
    {A A' B B' : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S} {σB : Spec B ⟶ S} {σB' : Spec B' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (fB : B' ⟶ B) (hfB : Spec.map fB ≫ σB' = σB)
    [RingHom.IsSquareZeroExtension fA.hom]
    [RingHom.IsSquareZeroExtension fB.hom]
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    (u : A' ⟶ B') (hu : Spec.map u ≫ σA' = σB')
    (sq : CommSq fA u v fB)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y)
    (x' : liftCat x fA hfA) :
    (infIso x x').hom ≫
        infinitesimalAutRestrict v (liftPullback fA hfA fB hfB v hv u hu sq x y φ) x' =
      infMap v hv (kernelHom fA fB v u sq) x y φ ≫
        (ModuleCat.restrictScalars v.hom).map
          (infIso y ((liftPullback fA hfA fB hfB v hv u hu sq x y φ).obj x')).hom :=
  sorry

/-- Naturality of the action `T_x(I) × Lift(x, A') ⟶ Lift(x, A')` in a morphism
of deformation situations. -/
theorem tangentAction_natural {S : Scheme.{u}} {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X]
    {A A' B B' : CommRingCat.{u}}
    {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S} {σB : Spec B ⟶ S} {σB' : Spec B' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (fB : B' ⟶ B) (hfB : Spec.map fB ≫ σB' = σB)
    [RingHom.IsSquareZeroExtension fA.hom]
    [RingHom.IsSquareZeroExtension fB.hom]
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    (u : A' ⟶ B') (hu : Spec.map u ≫ σA' = σB')
    (sq : CommSq fA u v fB)
    (x : X.p.Fiber (Over.mk σA)) (y : X.p.Fiber (Over.mk σB))
    (φ : Chosen.reindexObj X.p (specOverHom v hv) x ⟶ y)
    (t : (tangentFunctor x).obj (kernelObj fA))
    (ξ : lifts x fA hfA) :
    liftsMap (liftPullback fA hfA fB hfB v hv u hu sq x y φ) (tangentAction x t ξ) =
      tangentAction y (tangentMap v hv (kernelHom fA fB v u sq) x y φ t)
        (liftsMap (liftPullback fA hfA fB hfB v hv u hu sq x y φ) ξ) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
