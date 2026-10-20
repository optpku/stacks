/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt
public import ReasLib.AlgebraicGeometry.GroupoidsOver.RimSchlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.ResidueExtension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField.Extension

/-!
# Predeformation functor after a finite residue-field extension

A finite extension `l / κ(u0)` determines the morphism `u_{l,0} : Spec(l) ⟶ U`,
the slice object of `(Sch/U)_fppf` over `Spec(l)`, the restriction `x_{l,0}` of
an object `x` over `U`, and the induced morphism of predeformation categories
`ℱ_{(Sch/U)_fppf, l, u_{l,0}} ⟶ ℱ_{X, l, x_{l,0}}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open scoped BasedFunctor

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The morphism `u_{l,0} : Spec(l) ⟶ U` associated to a residue-field extension
`l / κ(u0)`. -/
def fromResidueExtension {U : Scheme.{u}} (u0 : U) (l : Type u) [Field l]
    [Algebra (residueFieldType u0) l] :
    Spec (CommRingCat.of l) ⟶ U :=
  Predeformation.residueHom (residueFieldType u0) l ≫ fromResidueField u0

/-- `fromResidueExtension u0 l` is `Spec` of `algebraMap κ(u0) l`, followed by
the canonical residue-field morphism of `u0`. -/
theorem fromResidueExtension_eq {U : Scheme.{u}} (u0 : U) (l : Type u) [Field l]
    [Algebra (residueFieldType u0) l] :
    fromResidueExtension u0 l =
      Spec.map (CommRingCat.ofHom (algebraMap (residueFieldType u0) l)) ≫
        fromResidueField u0 :=
  sorry

/-- The structure morphism `Spec(l) ⟶ S` of `fromResidueExtension` is `lToS` of
the canonical residue-field point of `u0`. -/
theorem fromResidueExtension_comp {S U : Scheme.{u}} (hU : U ⟶ S) (u0 : U)
    (l : Type u) [Field l] [Algebra (residueFieldType u0) l] :
    fromResidueExtension u0 l ≫ hU =
      Predeformation.lToS (residueFieldType u0) l (fromResidueField u0 ≫ hU) :=
  sorry

/-- The image of `fromResidueExtension u0 l` is the point `u0`. -/
theorem fromResidueExtension_image {U : Scheme.{u}} (u0 : U) (l : Type u)
    [Field l] [Algebra (residueFieldType u0) l] :
    Scheme.Hom.closedPointImage (fromResidueExtension u0 l) = u0 :=
  sorry

/-- The object of `(Sch/U)_fppf` given by `fromResidueExtension u0 l`. -/
def residueExtensionSliceObject {S : Scheme.{u}} {U : Scheme.{u}} (hU : U ⟶ S)
    (u0 : U) (l : Type u) [Field l] [Algebra (residueFieldType u0) l] :
    (GroupoidsOver.slice (Over.mk hU)).p.Fiber
      (Over.mk (fromResidueExtension u0 l ≫ hU)) :=
  ⟨Over.mk (Over.homMk (fromResidueExtension u0 l)
      rfl : Over.mk (fromResidueExtension u0 l ≫ hU) ⟶ Over.mk hU), rfl⟩

/-- `residueExtensionSliceObject hU u0 l` is the object of `Over U` given by
`fromResidueExtension u0 l`. -/
theorem residueExtensionSliceObject_spec {S : Scheme.{u}} {U : Scheme.{u}}
    (hU : U ⟶ S) (u0 : U) (l : Type u) [Field l]
    [Algebra (residueFieldType u0) l] :
    Functor.Fiber.fiberInclusion.obj (residueExtensionSliceObject hU u0 l) =
      Over.mk (Over.homMk (fromResidueExtension u0 l)
        rfl : Over.mk (fromResidueExtension u0 l ≫ hU) ⟶ Over.mk hU) :=
  sorry

/-- A finite residue-field extension of a finite type point remains locally of
finite type over `S`. -/
instance instLocallyOfFiniteType_fromResidueExtension {S U : Scheme.{u}}
    (hU : U ⟶ S) [LocallyOfFiniteType hU] (u0 : U) [IsFiniteTypePoint u0]
    (l : Type u) [Field l] [Algebra (residueFieldType u0) l]
    [Module.Finite (residueFieldType u0) l] :
    LocallyOfFiniteType (fromResidueExtension u0 l ≫ hU) :=
  sorry

/-- The restriction `x_{l,0}` of `x` to `Spec(l)`, obtained by evaluating the
2-Yoneda 1-morphism of `x` on `residueExtensionSliceObject`. -/
def residueExtensionObject {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) (l : Type u) [Field l]
    [Algebra (residueFieldType u0) l] :
    X.p.Fiber (Over.mk (fromResidueExtension u0 l ≫ hU)) :=
  Predeformation.residueImage (yonedaOfObject hU x hx)
    (residueExtensionSliceObject hU u0 l)

/-- `residueExtensionObject` is the image of `residueExtensionSliceObject` under
the fibre functor of `yonedaOfObject`. -/
theorem residueExtensionObject_spec {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) (l : Type u) [Field l]
    [Algebra (residueFieldType u0) l] :
    residueExtensionObject hU x hx u0 l =
      Predeformation.residueImage (yonedaOfObject hU x hx)
        (residueExtensionSliceObject hU u0 l) :=
  sorry

/-- The morphism of predeformation categories
`ℱ_{(Sch/U)_fppf, l, u_{l,0}} ⟶ ℱ_{X, l, x_{l,0}}` induced by the 2-Yoneda
1-morphism of `x` at the finite residue-field extension `l / κ(u0)`. -/
def hatResidueExtension {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU]
    (x : X.total) (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] (l : Type u) [Field l]
    [Algebra Λ l] [Module.Finite Λ l] [Algebra (residueFieldType u0) l]
    [Module.Finite (residueFieldType u0) l]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ openImmersion =
        fromResidueExtension u0 l ≫ hU) :
    Predeformation.predeformation openImmersion h_factor
        (GroupoidsOver.slice (Over.mk hU)) (residueExtensionSliceObject hU u0 l) ⥤ᵇ
      Predeformation.predeformation openImmersion h_factor X
        (residueExtensionObject hU x hx u0 l) :=
  Predeformation.map openImmersion h_factor (yonedaOfObject hU x hx)
    (residueExtensionSliceObject hU u0 l)

/-- `hatResidueExtension` is predeformation functoriality of `yonedaOfObject` at
the finite residue-field extension `l / κ(u0)`. -/
theorem hatResidueExtension_spec {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU]
    (x : X.total) (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] (l : Type u) [Field l]
    [Algebra Λ l] [Module.Finite Λ l] [Algebra (residueFieldType u0) l]
    [Module.Finite (residueFieldType u0) l]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ openImmersion =
        fromResidueExtension u0 l ≫ hU) :
    hatResidueExtension hU x hx u0 l openImmersion h_factor =
      Predeformation.map openImmersion h_factor (yonedaOfObject hU x hx)
        (residueExtensionSliceObject hU u0 l) :=
  sorry

/-- Over a locally Noetherian base, the Yoneda-induced predeformation functor
at a finite residue-field extension of a finite type point is smooth when the
object is versal at that point and its category fibred in groupoids satisfies
the Rim-Schlessinger condition. -/
instance instIsSmooth_hatResidueExtension {S : Scheme.{u}}
    [IsLocallyNoetherian S] {X : GroupoidsOver S} {U : Scheme.{u}}
    (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] (l : Type u) [Field l]
    [Algebra Λ l] [Module.Finite Λ l] [Algebra (residueFieldType u0) l]
    [Module.Finite (residueFieldType u0) l]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ openImmersion =
        fromResidueExtension u0 l ≫ hU)
    [HasRimSchlessinger X] [IsVersalAt hU x hx u0] :
    BasedFunctor.IsSmooth
      (hatResidueExtension hU x hx u0 l openImmersion h_factor) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
