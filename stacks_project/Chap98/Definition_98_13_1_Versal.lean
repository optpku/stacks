module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import stacks_project.Chap90.Definition_90_8_1_Smooth
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap98.«98_3_1_1_Functor»

/-!
# Versality at a finite type point

An object `x` of a category fibred in groupoids `X` over `(Sch/S)_fppf`, lying
over a scheme `U` locally of finite type over a locally Noetherian base `S`, is
versal at a finite type point `u0` of `U` when the morphism of predeformation
categories `hat x` of equation 98.12.1.1, at the canonical residue-field point
`Spec(κ(u0)) ⟶ U`, is smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The 2-Yoneda 1-morphism `(Sch/U)_fppf ⟶ X` associated to an object `x` of
`X` over `U`. -/
def yonedaOfObject {S : Scheme.{u}} {X : GroupoidsOver S} {U : Scheme.{u}}
    (hU : U ⟶ S) (x : X.total) (hx : X.p.obj x = Over.mk hU) :
    GroupoidsOver.slice (Over.mk hU) ⟶ X :=
  YonedaSlice.representative ⟨x, hx⟩

/-- The 2-Yoneda 1-morphism of `x` is the canonical slice representative of the
fibre object `⟨x, hx⟩`. -/
theorem yonedaOfObject_spec {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) (x : X.total)
    (hx : X.p.obj x = Over.mk hU) :
    yonedaOfObject hU x hx = YonedaSlice.representative ⟨x, hx⟩ :=
  sorry

/-- The identity object of the canonical slice fibration of `U` over `S`. -/
def sliceIdentityObject {S : Scheme.{u}} {U : Scheme.{u}} (hU : U ⟶ S) :
    (GroupoidsOver.slice (Over.mk hU)).total :=
  Over.mk (𝟙 (Over.mk hU))

/-- The identity slice object lies over `U ⟶ S`. -/
theorem sliceIdentityObject_over {S : Scheme.{u}} {U : Scheme.{u}}
    (hU : U ⟶ S) :
    (GroupoidsOver.slice (Over.mk hU)).p.obj (sliceIdentityObject hU) =
      Over.mk hU :=
  sorry

/-- Evaluating the 2-Yoneda 1-morphism of `x` on the identity slice object
recovers `x`. -/
theorem yonedaOfObject_apply_identity {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) (x : X.total)
    (hx : X.p.obj x = Over.mk hU) :
    (toFunctor (yonedaOfObject hU x hx)).obj (sliceIdentityObject hU) = x :=
  sorry

/-- The residue field `κ(u0)` as a type. -/
abbrev residueFieldType {U : Scheme.{u}} (u0 : U) : Type u :=
  U.residueField u0

/-- `residueFieldType u0` is the carrier of `U.residueField u0`. -/
theorem residueFieldType_spec {U : Scheme.{u}} (u0 : U) :
    CommRingCat.of (residueFieldType u0) = U.residueField u0 :=
  sorry

/-- The canonical morphism `Spec(κ(u0)) ⟶ U`. -/
abbrev fromResidueField {U : Scheme.{u}} (u0 : U) :
    Spec (CommRingCat.of (residueFieldType u0)) ⟶ U :=
  U.fromSpecResidueField u0

/-- `fromResidueField u0` is `U.fromSpecResidueField u0`. -/
theorem fromResidueField_eq {U : Scheme.{u}} (u0 : U) :
    fromResidueField u0 = U.fromSpecResidueField u0 :=
  sorry

/-- The object of `(Sch/U)_fppf` given by the canonical residue-field morphism
`Spec(κ(u0)) ⟶ U`. -/
def residueSliceObject {S : Scheme.{u}} {U : Scheme.{u}} (hU : U ⟶ S) (u0 : U) :
    (GroupoidsOver.slice (Over.mk hU)).p.Fiber
      (Over.mk (fromResidueField u0 ≫ hU)) :=
  ⟨Over.mk (Over.homMk (fromResidueField u0)
      rfl : Over.mk (fromResidueField u0 ≫ hU) ⟶ Over.mk hU), rfl⟩

/-- `residueSliceObject hU u0` is the object of `Over U` given by
`fromResidueField u0`. -/
theorem residueSliceObject_spec {S : Scheme.{u}} {U : Scheme.{u}} (hU : U ⟶ S)
    (u0 : U) :
    Functor.Fiber.fiberInclusion.obj (residueSliceObject hU u0) =
      Over.mk (Over.homMk (fromResidueField u0)
        rfl : Over.mk (fromResidueField u0 ≫ hU) ⟶ Over.mk hU) :=
  sorry

/-- The canonical residue-field point of a finite type point of a scheme locally
of finite type over `S` remains locally of finite type over `S`. -/
instance instLocallyOfFiniteType_residuePoint {S : Scheme.{u}} {U : Scheme.{u}}
    (hU : U ⟶ S) [LocallyOfFiniteType hU] (u0 : U) [IsFiniteTypePoint u0] :
    LocallyOfFiniteType (fromResidueField u0 ≫ hU) :=
  sorry

/-- The morphism `hat x` of predeformation categories at the canonical
residue-field point `U.fromSpecResidueField u0`, relative to an affine-open
factorization of `Spec(κ(u0)) ⟶ S`. This is predeformation functoriality of the
2-Yoneda 1-morphism of `x`. -/
def hat {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
          openImmersion =
        fromResidueField u0 ≫ hU) :=
  Predeformation.map openImmersion h_factor (yonedaOfObject hU x hx)
    (residueSliceObject hU u0)

/-- `hat` is predeformation functoriality of `yonedaOfObject` at the residue
field of `u0`. -/
theorem hat_spec {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
          openImmersion =
        fromResidueField u0 ≫ hU) :
    hat hU x hx u0 openImmersion h_factor =
      Predeformation.map openImmersion h_factor (yonedaOfObject hU x hx)
        (residueSliceObject hU u0) :=
  sorry

/-- The projection of a CFG-associated predeformation category is cofibered in
groupoids. -/
instance instIsFiberedInGroupoidsOp_predeformation
    {S : Scheme.{u}} [IsLocallyNoetherian S] {Λ k : Type u} [CommRing Λ]
    [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    {kToS : Spec (CommRingCat.of k) ⟶ S} [LocallyOfFiniteType kToS]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (X : GroupoidsOver S) (x0 : X.p.Fiber (Over.mk kToS)) :
    Functor.IsFibered.InGroupoids
      (Predeformation.predeformation openImmersion h_factor X x0).p.op :=
  sorry

/-- An object `x` of `X` over `U` is versal at a finite type point `u0` of `U`
when the morphism `hat x` of predeformation categories at `Spec(κ(u0)) ⟶ U` is
smooth. -/
class IsVersalAt {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) : Prop where
  /-- Smoothness of `hat x` on every affine-open factorization of
  `Spec(κ(u0)) ⟶ S`. -/
  isSmooth :
    ∀ [IsFiniteTypePoint u0] {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
      [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
      (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
      [IsOpenImmersion openImmersion]
      (h_factor :
        Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
            openImmersion =
          fromResidueField u0 ≫ hU),
      BasedFunctor.IsSmooth (hat hU x hx u0 openImmersion h_factor)

namespace IsVersalAt

/-- The identity object of a canonical slice fibration is versal at every finite
type point of the source scheme. -/
instance sliceId {S : Scheme.{u}} [IsLocallyNoetherian S] {U : Scheme.{u}}
    (hU : U ⟶ S) [LocallyOfFiniteType hU] (u0 : U) [IsFiniteTypePoint u0] :
    IsVersalAt hU (sliceIdentityObject hU) (sliceIdentityObject_over hU) u0 :=
  sorry

/-- Versality at `u0` supplies smoothness of the canonical residue-field
`hat x`. -/
theorem spec {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0]
    [IsVersalAt hU x hx u0]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
          openImmersion =
        fromResidueField u0 ≫ hU) :
    BasedFunctor.IsSmooth (hat hU x hx u0 openImmersion h_factor) :=
  sorry

/-- Versality at `u0` is smoothness of the canonical residue-field `hat x` on
every affine-open factorization of `Spec(κ(u0)) ⟶ S`. -/
theorem iff {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0] :
    IsVersalAt hU x hx u0 ↔
      ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
        [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
        (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
        [IsOpenImmersion openImmersion]
        (h_factor :
          Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
              openImmersion =
            fromResidueField u0 ≫ hU),
        BasedFunctor.IsSmooth (hat hU x hx u0 openImmersion h_factor) :=
  sorry

end IsVersalAt

/-- Unfolding `IsVersalAt` recovers smoothness of the canonical residue-field
`hat`. -/
theorem isVersalAt_iff {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU]
    (x : X.total) (hx : X.p.obj x = Over.mk hU) (u0 : U)
    [IsFiniteTypePoint u0] :
    IsVersalAt hU x hx u0 ↔
      ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
        [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
        (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
        [IsOpenImmersion openImmersion]
        (h_factor :
          Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
              openImmersion =
            fromResidueField u0 ≫ hU),
        BasedFunctor.IsSmooth (hat hU x hx u0 openImmersion h_factor) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
