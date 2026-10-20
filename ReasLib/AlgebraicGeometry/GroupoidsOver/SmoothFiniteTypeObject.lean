/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Core
public import ReasLib.AlgebraicGeometry.GroupoidsOver.MorphismProperty
public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt

/-!
# Smooth finite-type 2-Yoneda objects

A finite-type scheme `U ⟶ S` together with an object of a category fibred in
groupoids over `U` whose 2-Yoneda 1-morphism is smooth, approximating a given
residue object at a finite-type point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open AlgebraicGeometry.Groupoids
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Restriction morphism `Spec(κ(u0)) ⟶ U` in `Over S`. -/
def fromResidueFieldOverHom {S U : Scheme.{u}} (hU : U ⟶ S) (u0 : U) :
    Over.mk (fromResidueField u0 ≫ hU) ⟶ Over.mk hU :=
  Over.homMk (fromResidueField u0) rfl

/-- The underlying scheme morphism of `fromResidueFieldOverHom` is
`fromResidueField`. -/
theorem fromResidueFieldOverHom_left {S U : Scheme.{u}} (hU : U ⟶ S) (u0 : U) :
    (fromResidueFieldOverHom hU u0).left = fromResidueField u0 :=
  sorry

/-- Restriction of an object `x` of `X` over `U ⟶ S` along `Spec(κ(u0)) ⟶ U`. -/
def restrictToResidueField {S : Scheme.{u}} {X : GroupoidsOver S} {U : Scheme.{u}}
    (hU : U ⟶ S) (x : X.total) (hx : X.p.obj x = Over.mk hU) (u0 : U) :
    X.total :=
  IsPreFibered.pullbackObj hx (fromResidueFieldOverHom hU u0)

/-- `restrictToResidueField` is the chosen cartesian pullback along
`Over.homMk (fromResidueField u0)`. -/
theorem restrictToResidueField_eq {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) :
    restrictToResidueField hU x hx u0 =
      IsPreFibered.pullbackObj hx (fromResidueFieldOverHom hU u0) :=
  sorry

/-- The restricted object lies over `Spec(κ(u0)) ⟶ S`. -/
theorem restrictToResidueField_over {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) :
    X.p.obj (restrictToResidueField hU x hx u0) =
      Over.mk (fromResidueField u0 ≫ hU) :=
  sorry

/-- The restricted object `x|_{u0}` as an object of the fibre over
`Spec(κ(u0)) ⟶ S`. -/
def restrictToResidueFieldFiber {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) :
    X.p.Fiber (Over.mk (fromResidueField u0 ≫ hU)) :=
  Fiber.mk (restrictToResidueField_over hU x hx u0)

/-- `restrictToResidueFieldFiber` packages `restrictToResidueField` with
`restrictToResidueField_over`. -/
theorem restrictToResidueFieldFiber_eq {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) :
    restrictToResidueFieldFiber hU x hx u0 =
      Fiber.mk (restrictToResidueField_over hU x hx u0) :=
  sorry

/-- Transport of `Spec(k) ⟶ S` along a residue-field identification
`κ(u0) ≃+* k`, as a morphism in `Over S`. -/
def residueIsoOverHom {S : Scheme.{u}} {k : Type u} [Field k]
    (kToS : Spec (CommRingCat.of k) ⟶ S) {U : Scheme.{u}} (toS : U ⟶ S)
    (u0 : U) (residueIso : residueFieldType u0 ≃+* k)
    (residueIso_over :
      fromResidueField u0 ≫ toS =
        Spec.map (CommRingCat.ofHom residueIso.symm.toRingHom) ≫ kToS) :
    Over.mk (fromResidueField u0 ≫ toS) ⟶ Over.mk kToS :=
  Over.homMk (Spec.map (CommRingCat.ofHom residueIso.symm.toRingHom))
    residueIso_over.symm

/-- The underlying scheme morphism of `residueIsoOverHom` is `Spec` of
`residueIso.symm`. -/
theorem residueIsoOverHom_left {S : Scheme.{u}} {k : Type u} [Field k]
    (kToS : Spec (CommRingCat.of k) ⟶ S) {U : Scheme.{u}} (toS : U ⟶ S)
    (u0 : U) (residueIso : residueFieldType u0 ≃+* k)
    (residueIso_over :
      fromResidueField u0 ≫ toS =
        Spec.map (CommRingCat.ofHom residueIso.symm.toRingHom) ≫ kToS) :
    (residueIsoOverHom kToS toS u0 residueIso residueIso_over).left =
      Spec.map (CommRingCat.ofHom residueIso.symm.toRingHom) :=
  sorry

/-- Finite-type smooth 2-Yoneda data approximating a residue object `x0` over
`Spec(k) ⟶ S`: a finite type `U ⟶ S`, an object `x` over `U` whose 2-Yoneda
1-morphism is smooth, and a finite type point `u0` with residue field `k` such
that `x|_{u0} ≅ x0`. -/
def SmoothFiniteTypeObject {S : Scheme.{u}} {X : GroupoidsOver S}
    {k : Type u} [Field k] (kToS : Spec (CommRingCat.of k) ⟶ S)
    (x0 : X.p.Fiber (Over.mk kToS)) :=
  Σ' U : Scheme.{u},
    Σ' toS : U ⟶ S,
      Σ' finiteType : Scheme.Hom.FiniteType toS,
        Σ' object : X.total,
          Σ' over_obj : X.p.obj object = Over.mk toS,
            Σ' smooth : Groupoids.Hom.Smooth (yonedaOfObject toS object over_obj),
              Σ' u0 : U,
                Σ' isFiniteTypePoint : IsFiniteTypePoint u0,
                  Σ' residueIso : residueFieldType u0 ≃+* k,
                    Σ' residueIso_over :
                      fromResidueField u0 ≫ toS =
                        Spec.map (CommRingCat.ofHom residueIso.symm.toRingHom) ≫ kToS,
                      restrictToResidueFieldFiber toS object over_obj u0 ≅
                        Chosen.reindexObj X.p
                          (residueIsoOverHom kToS toS u0 residueIso residueIso_over) x0

namespace SmoothFiniteTypeObject

variable {S : Scheme.{u}} {X : GroupoidsOver S}
variable {k : Type u} [Field k] {kToS : Spec (CommRingCat.of k) ⟶ S}
variable {x0 : X.p.Fiber (Over.mk kToS)}

/-- The finite-type chart scheme. -/
def U (W : SmoothFiniteTypeObject kToS x0) :
    Scheme.{u} := W.1

/-- The structure morphism of the chart. -/
def toS (W : SmoothFiniteTypeObject kToS x0) :
    W.U ⟶ S := W.2.1

/-- The structure morphism of the chart is of finite type. -/
def finiteType (W : SmoothFiniteTypeObject kToS x0) :
    _root_.AlgebraicGeometry.Scheme.Hom.FiniteType W.toS := W.2.2.1

/-- The structure morphism of the chart is quasi-compact. -/
instance quasiCompact (W : SmoothFiniteTypeObject kToS x0) :
    _root_.AlgebraicGeometry.QuasiCompact W.toS := W.finiteType.toQuasiCompact

/-- The structure morphism of the chart is locally of finite type. -/
instance locallyOfFiniteType (W : SmoothFiniteTypeObject kToS x0) :
    _root_.AlgebraicGeometry.LocallyOfFiniteType W.toS := W.finiteType.toLocallyOfFiniteType

/-- The object over the chart scheme. -/
def object (W : SmoothFiniteTypeObject kToS x0) :
    X.total := W.2.2.2.1

/-- The chart object lies over its structure morphism. -/
def over_obj (W : SmoothFiniteTypeObject kToS x0) :
    X.p.obj W.object = Over.mk W.toS := W.2.2.2.2.1

/-- The Yoneda morphism of the chart object is smooth. -/
def smooth (W : SmoothFiniteTypeObject kToS x0) :
    _root_.AlgebraicGeometry.Groupoids.Hom.Smooth
      (yonedaOfObject W.toS W.object W.over_obj) := W.2.2.2.2.2.1

/-- The distinguished finite-type point of the chart. -/
def u0 (W : SmoothFiniteTypeObject kToS x0) :
    W.U := W.2.2.2.2.2.2.1

/-- The distinguished chart point is of finite type. -/
instance isFiniteTypePoint (W : SmoothFiniteTypeObject kToS x0) :
    IsFiniteTypePoint W.u0 := W.2.2.2.2.2.2.2.1

/-- The identification of the distinguished residue field with the given field. -/
def residueIso (W : SmoothFiniteTypeObject kToS x0) :
    residueFieldType W.u0 ≃+* k := W.2.2.2.2.2.2.2.2.1

/-- The residue-field identification commutes with the morphisms to the base. -/
def residueIso_over (W : SmoothFiniteTypeObject kToS x0) :
    fromResidueField W.u0 ≫ W.toS =
      Spec.map (CommRingCat.ofHom W.residueIso.symm.toRingHom) ≫ kToS := W.2.2.2.2.2.2.2.2.2.1

/-- The restricted chart object is isomorphic in the fibre to the transported residue object. -/
def restrictIso (W : SmoothFiniteTypeObject kToS x0) :
    restrictToResidueFieldFiber W.toS W.object W.over_obj W.u0 ≅
      Chosen.reindexObj X.p
        (residueIsoOverHom kToS W.toS W.u0 W.residueIso W.residueIso_over) x0 := W.2.2.2.2.2.2.2.2.2.2

/-- Package finite-type smooth 2-Yoneda data approximating a residue object. -/
def of (U : Scheme.{u}) (toS : U ⟶ S) [Scheme.Hom.FiniteType toS]
    (object : X.total) (over_obj : X.p.obj object = Over.mk toS)
    [Groupoids.Hom.Smooth (yonedaOfObject toS object over_obj)] (u0 : U)
    [IsFiniteTypePoint u0] (residueIso : residueFieldType u0 ≃+* k)
    (residueIso_over :
      fromResidueField u0 ≫ toS =
        Spec.map (CommRingCat.ofHom residueIso.symm.toRingHom) ≫ kToS)
    (restrictIso :
      restrictToResidueFieldFiber toS object over_obj u0 ≅
        Chosen.reindexObj X.p
          (residueIsoOverHom kToS toS u0 residueIso residueIso_over) x0) :
    SmoothFiniteTypeObject kToS x0 :=
  ⟨U, toS, inferInstance, object, over_obj, inferInstance, u0, inferInstance,
    residueIso, residueIso_over, restrictIso⟩

/-- Smooth finite-type 2-Yoneda data have a finite type
structure morphism, smoothness of the 2-Yoneda 1-morphism, finite type point,
residue-field identification over `S`, and `x|_{u0} ≅ x0`. -/
theorem spec (W : SmoothFiniteTypeObject kToS x0) :
    Scheme.Hom.FiniteType W.toS ∧
      Groupoids.Hom.Smooth (yonedaOfObject W.toS W.object W.over_obj) ∧
        IsFiniteTypePoint W.u0 ∧
          (fromResidueField W.u0 ≫ W.toS =
            Spec.map (CommRingCat.ofHom W.residueIso.symm.toRingHom) ≫ kToS) ∧
            Nonempty
              (restrictToResidueFieldFiber W.toS W.object W.over_obj W.u0 ≅
                Chosen.reindexObj X.p
                  (residueIsoOverHom kToS W.toS W.u0 W.residueIso
                    W.residueIso_over)
                  x0) :=
  sorry

/-- The restricted object `x|_{u0}` is isomorphic to `x0` after transport
along `residueIso`. -/
theorem exists_restrictIso (W : SmoothFiniteTypeObject kToS x0) :
    Nonempty
      (restrictToResidueFieldFiber W.toS W.object W.over_obj W.u0 ≅
        Chosen.reindexObj X.p
          (residueIsoOverHom kToS W.toS W.u0 W.residueIso W.residueIso_over)
          x0) :=
  sorry

end SmoothFiniteTypeObject

end AlgebraicGeometry.GroupoidsOver
