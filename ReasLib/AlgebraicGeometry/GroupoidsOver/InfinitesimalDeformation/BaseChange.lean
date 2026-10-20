/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalDeformation.Functoriality

/-!
# Scalar extension of infinitesimal automorphism modules

An `S`-algebra map `A ⟶ B` induces a canonical comparison
`Inf_x(M) ⊗[A] B ⟶ Inf_y(M ⊗[A] B)`, where `y` is the restriction of the
fibre object `x` along `Spec.map v`. The map is the adjunct of `infMap`
along the extension/restriction-of-scalars unit.
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

end AlgebraicGeometry.GroupoidsOver

