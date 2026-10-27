/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalDeformation.Functoriality

/-!
# Scalar extension of infinitesimal automorphism and tangent modules

An `S`-algebra map `A ⟶ B` induces a canonical comparison
`Inf_x(M) ⊗[A] B ⟶ Inf_y(M ⊗[A] B)`, where `y` is the restriction of the
fibre object `x` along `Spec.map v`. It also induces the tangent comparison
`T_x(M) ⊗[A] B ⟶ T_y(M ⊗[A] B)`. These maps are the adjuncts of `infMap`
and `tangentMap` along the extension/restriction-of-scalars unit.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The canonical `B`-linear comparison
`Inf_x(M) ⊗[A] B ⟶ Inf_y(M ⊗[A] B)` along an `S`-algebra map `v : A ⟶ B`,
where `y` is the restriction of `x` along `Spec.map v`. -/
def infExtendScalars {S : Scheme.{u}} {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X]
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars v.hom).obj ((infFunctor x).obj M) ⟶
      (infFunctor (Chosen.reindexObj X.p (specOverHom v hv) x)).obj
        ((ModuleCat.extendScalars v.hom).obj M) :=
  let y := Chosen.reindexObj X.p (specOverHom v hv) x
  let adj := ModuleCat.extendRestrictScalarsAdj v.hom
  (adj.homEquiv _ _).symm (infMap v hv (adj.unit.app M) x y (𝟙 y))

/-- `infExtendScalars` is the adjunct of `infMap` along the
extension-of-scalars unit of `M`. -/
theorem infExtendScalars_apply {S : Scheme.{u}} {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X]
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    (ModuleCat.extendRestrictScalarsAdj v.hom).homEquiv
        ((infFunctor x).obj M)
        ((infFunctor (Chosen.reindexObj X.p (specOverHom v hv) x)).obj
          ((ModuleCat.extendScalars v.hom).obj M))
        (infExtendScalars v hv x M) =
      infMap v hv ((ModuleCat.extendRestrictScalarsAdj v.hom).unit.app M) x
        (Chosen.reindexObj X.p (specOverHom v hv) x)
        (𝟙 (Chosen.reindexObj X.p (specOverHom v hv) x)) :=
  sorry

/-- The canonical `B`-linear comparison
`T_x(M) ⊗[A] B ⟶ T_y(M ⊗[A] B)` along an `S`-algebra map `v : A ⟶ B`,
where `y` is the restriction of `x` along `Spec.map v`. -/
def tangentExtendScalars {S : Scheme.{u}} {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X]
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars.{u, u, u + 1} v.hom).obj ((tangentFunctor x).obj M) ⟶
      (tangentFunctor (Chosen.reindexObj X.p (specOverHom v hv) x)).obj
        ((ModuleCat.extendScalars.{u, u, u} v.hom).obj M) :=
  let y := Chosen.reindexObj X.p (specOverHom v hv) x
  let adjM := ModuleCat.extendRestrictScalarsAdj.{u, u, u} v.hom
  let adjT := ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} v.hom
  (adjT.homEquiv _ _).symm (tangentMap v hv (adjM.unit.app M) x y (𝟙 y))

/-- `tangentExtendScalars` is the adjunct of `tangentMap` along the
extension-of-scalars unit of `M`. -/
theorem tangentExtendScalars_apply {S : Scheme.{u}} {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X]
    {A B : CommRingCat.{u}} {σA : Spec A ⟶ S} {σB : Spec B ⟶ S}
    (v : A ⟶ B) (hv : Spec.map v ≫ σA = σB)
    (x : X.p.Fiber (Over.mk σA)) (M : ModuleCat.{u} A) :
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} v.hom).homEquiv
        ((tangentFunctor x).obj M)
        ((tangentFunctor (Chosen.reindexObj X.p (specOverHom v hv) x)).obj
          ((ModuleCat.extendScalars.{u, u, u} v.hom).obj M))
        (tangentExtendScalars v hv x M) =
      tangentMap v hv ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} v.hom).unit.app M) x
        (Chosen.reindexObj X.p (specOverHom v hv) x)
        (𝟙 (Chosen.reindexObj X.p (specOverHom v hv) x)) := sorry

end AlgebraicGeometry.GroupoidsOver

