/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable
public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt

/-!
# Representing a Yoneda two-fibre product with both projections

A representing algebraic space identifies both projections of the two-fibre
product under a single equivalence of groupoid fibrations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The algebraic space `Z` over `S`, together with morphisms `toV` and `toU`,
represents the 2-fibre product of the 2-Yoneda 1-morphisms of `y` and `x`. -/
def representsYonedaFibreProduct {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) (x : X.total) (hx : X.p.obj x = Over.mk hU)
    {V : Scheme.{u}} (hV : V ⟶ S) (y : X.total) (hy : X.p.obj y = Over.mk hV)
    (Z : AlgebraicSpace S) (toV : Z ⟶ AlgebraicSpace.ofOver (Over.mk hV))
    (toU : Z ⟶ AlgebraicSpace.ofOver (Over.mk hU)) : Prop :=
  ∃ e : TwoFibreProduct.apex.{u + 1, u, u + 1, u}
      (yonedaOfObject hV y hy) (yonedaOfObject hU x hx) ≌
      Z.toGroupoids,
    Nonempty
        (e.hom ≫ AlgebraicSpace.toGroupoids.map toV ≫
            (AlgebraicSpace.ofOverSliceEquiv (Over.mk hV)).hom ≅
          TwoFibreProduct.fst.{u + 1, u, u + 1, u}
            (yonedaOfObject hV y hy) (yonedaOfObject hU x hx)) ∧
      Nonempty
        (e.hom ≫ AlgebraicSpace.toGroupoids.map toU ≫
            (AlgebraicSpace.ofOverSliceEquiv (Over.mk hU)).hom ≅
          TwoFibreProduct.snd.{u + 1, u, u + 1, u}
            (yonedaOfObject hV y hy) (yonedaOfObject hU x hx))

/-- Unfolding `representsYonedaFibreProduct` recovers a shared equivalence of
the Yoneda 2-fibre product with `Z.toGroupoids` and both projection triangles. -/
theorem representsYonedaFibreProduct_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) (x : X.total) (hx : X.p.obj x = Over.mk hU)
    {V : Scheme.{u}} (hV : V ⟶ S) (y : X.total) (hy : X.p.obj y = Over.mk hV)
    (Z : AlgebraicSpace S) (toV : Z ⟶ AlgebraicSpace.ofOver (Over.mk hV))
    (toU : Z ⟶ AlgebraicSpace.ofOver (Over.mk hU)) :
    representsYonedaFibreProduct hU x hx hV y hy Z toV toU ↔
      ∃ e : TwoFibreProduct.apex.{u + 1, u, u + 1, u}
          (yonedaOfObject hV y hy) (yonedaOfObject hU x hx) ≌
          Z.toGroupoids,
        Nonempty
            (e.hom ≫ AlgebraicSpace.toGroupoids.map toV ≫
                (AlgebraicSpace.ofOverSliceEquiv (Over.mk hV)).hom ≅
              TwoFibreProduct.fst.{u + 1, u, u + 1, u}
                (yonedaOfObject hV y hy) (yonedaOfObject hU x hx)) ∧
          Nonempty
            (e.hom ≫ AlgebraicSpace.toGroupoids.map toU ≫
                (AlgebraicSpace.ofOverSliceEquiv (Over.mk hU)).hom ≅
              TwoFibreProduct.snd.{u + 1, u, u + 1, u}
                (yonedaOfObject hV y hy) (yonedaOfObject hU x hx)) :=
  sorry

/-- A representing pair of projections yields `RepresentsBaseChange` for the
Yoneda 1-morphism of `x` along the Yoneda 1-morphism of `y`. -/
theorem representsYonedaFibreProduct.representsBaseChange
    {S : Scheme.{u}} {X : GroupoidsOver S} {U : Scheme.{u}} (hU : U ⟶ S)
    (x : X.total) (hx : X.p.obj x = Over.mk hU) {V : Scheme.{u}} (hV : V ⟶ S)
    (y : X.total) (hy : X.p.obj y = Over.mk hV) (Z : AlgebraicSpace S)
    (toV : Z ⟶ AlgebraicSpace.ofOver (Over.mk hV))
    (toU : Z ⟶ AlgebraicSpace.ofOver (Over.mk hU))
    (hZ : representsYonedaFibreProduct hU x hx hV y hy Z toV toU) :
    RepresentsBaseChange (yonedaOfObject hU x hx) (yonedaOfObject hV y hy)
      Z toV :=
  sorry

end AlgebraicGeometry.GroupoidsOver
