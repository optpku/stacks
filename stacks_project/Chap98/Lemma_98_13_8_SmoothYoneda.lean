/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Core
public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty
public import stacks_project.Chap98.Definition_98_13_1_Versal

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

/-- Transport of a residue object `x0` along `residueIso`, as an object of `X`. -/
def reindexResidueObject {S : Scheme.{u}} {X : GroupoidsOver S} {k : Type u}
    [Field k] {kToS : Spec (CommRingCat.of k) ⟶ S}
    (x0 : X.p.Fiber (Over.mk kToS)) {U : Scheme.{u}} (toS : U ⟶ S) (u0 : U)
    (residueIso : residueFieldType u0 ≃+* k)
    (residueIso_over :
      fromResidueField u0 ≫ toS =
        Spec.map (CommRingCat.ofHom residueIso.symm.toRingHom) ≫ kToS) :
    X.total :=
  (Chosen.reindexObj X.p
      (residueIsoOverHom kToS toS u0 residueIso residueIso_over) x0).1

/-- `reindexResidueObject` is the total object of the chosen reindexing of `x0`
along `residueIsoOverHom`. -/
theorem reindexResidueObject_eq {S : Scheme.{u}} {X : GroupoidsOver S}
    {k : Type u} [Field k] {kToS : Spec (CommRingCat.of k) ⟶ S}
    (x0 : X.p.Fiber (Over.mk kToS)) {U : Scheme.{u}} (toS : U ⟶ S) (u0 : U)
    (residueIso : residueFieldType u0 ≃+* k)
    (residueIso_over :
      fromResidueField u0 ≫ toS =
        Spec.map (CommRingCat.ofHom residueIso.symm.toRingHom) ≫ kToS) :
    reindexResidueObject x0 toS u0 residueIso residueIso_over =
      (Chosen.reindexObj X.p
          (residueIsoOverHom kToS toS u0 residueIso residueIso_over) x0).1 :=
  sorry

/-- Finite-type smooth 2-Yoneda data approximating a residue object `x0` over
`Spec(k) ⟶ S`: a finite type `U ⟶ S`, an object `x` over `U` whose 2-Yoneda
1-morphism is smooth, and a finite type point `u0` with residue field `k` such
that `x|_{u0} ≅ x0`. -/
structure SmoothFiniteTypeObject {S : Scheme.{u}} {X : GroupoidsOver S}
    {k : Type u} [Field k] (kToS : Spec (CommRingCat.of k) ⟶ S)
    (x0 : X.p.Fiber (Over.mk kToS)) where
  /-- Finite-type scheme over `S`. -/
  U : Scheme.{u}
  /-- Structure morphism `U ⟶ S`. -/
  toS : U ⟶ S
  [finiteType : Scheme.Hom.FiniteType toS]
  /-- Object of `X` over `U`. -/
  object : X.total
  /-- The object lies over `U ⟶ S`. -/
  over_obj : X.p.obj object = Over.mk toS
  [smooth : Groupoids.Hom.Smooth (yonedaOfObject toS object over_obj)]
  /-- Finite type point of `U` with residue field `k`. -/
  u0 : U
  [isFiniteTypePoint : IsFiniteTypePoint u0]
  /-- Identification `κ(u0) ≃+* k` of residue fields. -/
  residueIso : residueFieldType u0 ≃+* k
  /-- `Spec(κ(u0)) ⟶ S` agrees with `Spec(k) ⟶ S` after `residueIso`. -/
  residueIso_over :
    fromResidueField u0 ≫ toS =
      Spec.map (CommRingCat.ofHom residueIso.symm.toRingHom) ≫ kToS
  /-- Fibre isomorphism `x|_{u0} ≅ x0` over `𝟙`, after transporting `x0` along
  `residueIso`. -/
  restrictIso :
    restrictToResidueFieldFiber toS object over_obj u0 ≅
      Chosen.reindexObj X.p
        (residueIsoOverHom kToS toS u0 residueIso residueIso_over) x0

attribute [instance] SmoothFiniteTypeObject.finiteType
  SmoothFiniteTypeObject.isFiniteTypePoint SmoothFiniteTypeObject.smooth

namespace SmoothFiniteTypeObject

variable {S : Scheme.{u}} {X : GroupoidsOver S}
variable {k : Type u} [Field k] {kToS : Spec (CommRingCat.of k) ⟶ S}
variable {x0 : X.p.Fiber (Over.mk kToS)}

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
    SmoothFiniteTypeObject kToS x0 where
  U := U
  toS := toS
  object := object
  over_obj := over_obj
  u0 := u0
  residueIso := residueIso
  residueIso_over := residueIso_over
  restrictIso := restrictIso

/-- Source conditions encoded by smooth finite-type 2-Yoneda data: finite type
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

/-- Existence of smooth finite-type 2-Yoneda data is equivalent to the source
conditions of a finite type `U ⟶ S`, a smooth 2-Yoneda 1-morphism, and a finite
type point `u0` with residue field `k` such that `x|_{u0} ≅ x0`. -/
theorem spec_iff :
    Nonempty (SmoothFiniteTypeObject kToS x0) ↔
      ∃ W : SmoothFiniteTypeObject kToS x0,
        Scheme.Hom.FiniteType W.toS ∧
          Groupoids.Hom.Smooth (yonedaOfObject W.toS W.object W.over_obj) ∧
            IsFiniteTypePoint W.u0 ∧
              (fromResidueField W.u0 ≫ W.toS =
                Spec.map (CommRingCat.ofHom W.residueIso.symm.toRingHom) ≫
                  kToS) ∧
                Nonempty
                  (restrictToResidueFieldFiber W.toS W.object W.over_obj W.u0 ≅
                    Chosen.reindexObj X.p
                      (residueIsoOverHom kToS W.toS W.u0 W.residueIso
                        W.residueIso_over)
                      x0) :=
  sorry

/-- Source restriction clause: `x|_{u0}` is isomorphic to `x0` after transport
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
