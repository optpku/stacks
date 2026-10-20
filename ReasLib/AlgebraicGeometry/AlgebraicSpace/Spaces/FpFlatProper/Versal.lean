module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProper.Predeformation

/-!
# Versality of `Spaces'_{fp, flat, proper}` at finite type points

The cartesian restriction of an object of `FpFlatProperGroupoids S` along a
morphism of test schemes, the induced morphism `hat` of predeformation
categories at a residue field, and the resulting pointwise versality
predicate. Hom-types of `FpFlatProperGroupoids S` live in `Type (u + 1)`, so
this cannot be an instance of `AlgebraicGeometry.GroupoidsOver.IsVersalAt`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Functor
open CategoryTheory.Limits
open AlgebraicGeometry.GroupoidsOver
  (residueFieldType fromResidueField residueSliceObject)
open AlgebraicGeometry.GroupoidsOver.Predeformation
  (specOver specOverMap specOver_toResidue)
open AlgebraicGeometry.AlgebraicSpace.Spaces
open scoped BasedFunctor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids

/-- The underlying algebraic space of an object of `FpFlatProperGroupoids S`. -/
abbrev space {S : Scheme.{u}} (x : FpFlatProperGroupoids S) : AlgebraicSpace S :=
  x.obj.obj.obj.left

/-- The structure morphism of an object of `FpFlatProperGroupoids S`. -/
def structureHom {S : Scheme.{u}} (x : FpFlatProperGroupoids S) :
    space x ⟶ ofOver ((pFpFlatProperGroupoids S).obj x) :=
  x.obj.obj.obj.hom

/-- The algebraic space of `mk pX` is the source of `pX`. -/
theorem space_mk {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (pX : X ⟶ ofOver U) [FpFlatProper pX] : space (mk pX) = X :=
  sorry

/-- The structure morphism of `mk pX` is `pX`. -/
theorem structureHom_mk {S : Scheme.{u}} {U : Over S} {X : AlgebraicSpace S}
    (pX : X ⟶ ofOver U) [FpFlatProper pX] : structureHom (mk pX) = pX :=
  sorry

/-- The cartesian restriction of an object of `FpFlatProperGroupoids S` along a
morphism of test schemes, as the algebraic-space pullback of the structure
morphism. -/
def restrictAlong {S : Scheme.{u}} (x : FpFlatProperGroupoids S) {T : Over S}
    (h : T ⟶ (pFpFlatProperGroupoids S).obj x) : FpFlatProperGroupoids S := by
  let pX := pullback.snd (structureHom x) ((ofOverFunctor S).map h)
  have laws : FiniteType pX ∧ FpFlatProper pX := by
    sorry
  exact
    { obj := { obj := { obj := Spaces.mk pX, property := laws.1 } }
      property := laws.2 }

/-- The test scheme of `restrictAlong x h` is the source of `h`. -/
theorem restrictAlong_p {S : Scheme.{u}} (x : FpFlatProperGroupoids S)
    {T : Over S} (h : T ⟶ (pFpFlatProperGroupoids S).obj x) :
    (pFpFlatProperGroupoids S).obj (restrictAlong x h) = T :=
  sorry

/-- `restrictAlong x h` is the pullback of `structureHom x` along
`ofOverFunctor.map h`. -/
theorem restrictAlong_spec {S : Scheme.{u}} (x : FpFlatProperGroupoids S)
    {T : Over S} (h : T ⟶ (pFpFlatProperGroupoids S).obj x) :
    (pFpFlatProperGroupoids S).obj (restrictAlong x h) = T ∧
      structureHom (restrictAlong x h) =
        pullback.snd (structureHom x) ((ofOverFunctor S).map h) :=
  sorry

/-- The algebraic-space map of cartesian restriction along a composite
test-scheme morphism. -/
def restrictAlong_hom_left {S : Scheme.{u}} (x : FpFlatProperGroupoids S)
    {T T' : Over S} (h : T' ⟶ (pFpFlatProperGroupoids S).obj x) (φ : T ⟶ T') :
    pullback (structureHom x) ((ofOverFunctor S).map (φ ≫ h)) ⟶
      pullback (structureHom x) ((ofOverFunctor S).map h) :=
  pullback.map (structureHom x) ((ofOverFunctor S).map (φ ≫ h))
    (structureHom x) ((ofOverFunctor S).map h) (𝟙 (space x))
    ((ofOverFunctor S).map φ)
    (𝟙 (ofOver ((pFpFlatProperGroupoids S).obj x)))
    ((Category.comp_id (structureHom x)).trans (Category.id_comp (structureHom x)).symm)
    ((Category.comp_id ((ofOverFunctor S).map (φ ≫ h))).trans
      ((ofOverFunctor S).map_comp φ h).symm)

/-- The left map of restriction along `φ ≫ h` commutes with the pullback
projections over `φ`. -/
theorem restrictAlong_hom_left_snd {S : Scheme.{u}}
    (x : FpFlatProperGroupoids S) {T T' : Over S}
    (h : T' ⟶ (pFpFlatProperGroupoids S).obj x) (φ : T ⟶ T') :
    restrictAlong_hom_left x h φ ≫
        pullback.snd (structureHom x) ((ofOverFunctor S).map h) =
      pullback.snd (structureHom x) ((ofOverFunctor S).map (φ ≫ h)) ≫
        (ofOverFunctor S).map φ :=
  sorry

/-- The cartesian morphism `restrictAlong x (φ ≫ h) ⟶ restrictAlong x h`. -/
def restrictAlong_hom {S : Scheme.{u}} (x : FpFlatProperGroupoids S)
    {T T' : Over S} (h : T' ⟶ (pFpFlatProperGroupoids S).obj x) (φ : T ⟶ T') :
    restrictAlong x (φ ≫ h) ⟶ restrictAlong x h := by
  let commutativity :=
    restrictAlong_hom_left x h φ ≫ structureHom (restrictAlong x h) =
      structureHom (restrictAlong x (φ ≫ h)) ≫ (ofOverFunctor S).map φ
  let square (w : commutativity) :
      (restrictAlong x (φ ≫ h)).obj.obj ⟶ (restrictAlong x h).obj.obj :=
    { hom := { left := restrictAlong_hom_left x h φ, right := φ, w := w } }
  have laws : commutativity ∧
      ∀ w : commutativity,
        Functor.IsStronglyCartesian.property ((finiteType S).ι ⋙ Spaces.p) (square w) := by
    sorry
  exact { hom := { hom := square laws.1, property := laws.2 laws.1 } }

/-- The projection of `restrictAlong_hom x h φ` is the test-scheme morphism `φ`. -/
theorem restrictAlong_hom_p {S : Scheme.{u}} (x : FpFlatProperGroupoids S)
    {T T' : Over S} (h : T' ⟶ (pFpFlatProperGroupoids S).obj x) (φ : T ⟶ T') :
    (pFpFlatProperGroupoids S).map (restrictAlong_hom x h φ) = φ :=
  sorry

/-- Transport of cartesian restrictions along an equality of test-scheme
morphisms. -/
def restrictAlong_congr {S : Scheme.{u}} (x : FpFlatProperGroupoids S)
    {T : Over S} {h₁ h₂ : T ⟶ (pFpFlatProperGroupoids S).obj x} (e : h₁ = h₂) :
    restrictAlong x h₁ ⟶ restrictAlong x h₂ :=
  eqToHom (congrArg (restrictAlong x) e)

variable {S : Scheme.{u}} {U : Scheme.{u}} (hU : U ⟶ S)

/-- The morphism `Spec(κ(u0)) ⟶ U` over `S`, as an arrow into the test scheme of
`x`. -/
def residueToObj (x : FpFlatProperGroupoids S)
    (hx : (pFpFlatProperGroupoids S).obj x = Over.mk hU) (u0 : U) :
    Over.mk (fromResidueField u0 ≫ hU) ⟶ (pFpFlatProperGroupoids S).obj x :=
  (Over.homMk (fromResidueField u0) :
      Over.mk (fromResidueField u0 ≫ hU) ⟶ Over.mk hU) ≫
    eqToHom hx.symm

/-- The residue object of `x` at a point `u0`, obtained by cartesian restriction
along `Spec(κ(u0)) ⟶ U`. -/
def residueObj (x : FpFlatProperGroupoids S)
    (hx : (pFpFlatProperGroupoids S).obj x = Over.mk hU) (u0 : U) :
    (pFpFlatProperGroupoids S).Fiber (Over.mk (fromResidueField u0 ≫ hU)) :=
  ⟨restrictAlong x (residueToObj hU x hx u0), sorry⟩

/-- `residueObj` is the cartesian restriction of `x` along
`fromResidueField u0`. -/
theorem residueObj_spec (x : FpFlatProperGroupoids S)
    (hx : (pFpFlatProperGroupoids S).obj x = Over.mk hU) (u0 : U) :
    Fiber.fiberInclusion.obj (residueObj hU x hx u0) =
      restrictAlong x (residueToObj hU x hx u0) :=
  sorry

/-- The arrow `Spec(A) ⟶ U` over `S` carried by a slice predeformation object, as
an arrow into the test scheme of `x`. -/
def specToObj [AlgebraicGeometry.IsLocallyNoetherian S] (x : FpFlatProperGroupoids S)
    (hx : (pFpFlatProperGroupoids S).obj x = Over.mk hU) (u0 : U)
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [AlgebraicGeometry.IsOpenImmersion openImmersion]
    [AlgebraicGeometry.LocallyOfFiniteType (fromResidueField u0 ≫ hU)]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
          openImmersion =
        fromResidueField u0 ≫ hU)
    (ξ :
      AlgebraicGeometry.GroupoidsOver.Predeformation.Obj openImmersion
        (fromResidueField u0 ≫ hU) h_factor (GroupoidsOver.slice (Over.mk hU))
        (residueSliceObject hU u0)) :
    (Fiber.fiberInclusion.obj ξ.target).left ⟶ (pFpFlatProperGroupoids S).obj x :=
  (Fiber.fiberInclusion.obj ξ.target).hom ≫ eqToHom hx.symm

/-- The object of `ℱ_{Spaces'_{fp, flat, proper}, κ(u0), x0}` obtained by
restricting `x` along the Artinian test scheme of a slice predeformation
object. -/
def hatObj [AlgebraicGeometry.IsLocallyNoetherian S] (x : FpFlatProperGroupoids S)
    (hx : (pFpFlatProperGroupoids S).obj x = Over.mk hU) (u0 : U)
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [AlgebraicGeometry.IsOpenImmersion openImmersion]
    [AlgebraicGeometry.LocallyOfFiniteType (fromResidueField u0 ≫ hU)]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
          openImmersion =
        fromResidueField u0 ≫ hU)
    (ξ :
      AlgebraicGeometry.GroupoidsOver.Predeformation.Obj openImmersion
        (fromResidueField u0 ≫ hU) h_factor (GroupoidsOver.slice (Over.mk hU))
        (residueSliceObject hU u0)) :
    Predeformation.Obj openImmersion (fromResidueField u0 ≫ hU) h_factor
      (residueObj hU x hx u0) := by
  let target := restrictAlong x (specToObj hU x hx u0 openImmersion h_factor ξ)
  let fromResidue : Fiber.fiberInclusion.obj (residueObj hU x hx u0) ⟶ target :=
    restrictAlong_congr x
        ((congrArg (fun i ↦ i ≫ eqToHom hx.symm) ξ.fromResidue.w.symm).trans
          (Category.assoc _ _ _)) ≫
      restrictAlong_hom x (specToObj hU x hx u0 openImmersion h_factor ξ)
        ξ.fromResidue.left
  have laws : (pFpFlatProperGroupoids S).obj target = specOver openImmersion ξ.base ∧
      (pFpFlatProperGroupoids S).IsHomLift
        (specOver_toResidue openImmersion (fromResidueField u0 ≫ hU) h_factor ξ.base)
        fromResidue := by
    sorry
  exact Predeformation.Obj.of openImmersion (fromResidueField u0 ≫ hU) h_factor
    (residueObj hU x hx u0) ξ.base ⟨target, laws.1⟩ fromResidue laws.2

/-- The reversed arrow in `FpFlatProperGroupoids S` induced by a morphism of
slice predeformation categories. -/
def hatHom [AlgebraicGeometry.IsLocallyNoetherian S] (x : FpFlatProperGroupoids S)
    (hx : (pFpFlatProperGroupoids S).obj x = Over.mk hU) (u0 : U)
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [AlgebraicGeometry.IsOpenImmersion openImmersion]
    [AlgebraicGeometry.LocallyOfFiniteType (fromResidueField u0 ≫ hU)]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
          openImmersion =
        fromResidueField u0 ≫ hU)
    {ξ η :
      AlgebraicGeometry.GroupoidsOver.Predeformation.Obj openImmersion
        (fromResidueField u0 ≫ hU) h_factor (GroupoidsOver.slice (Over.mk hU))
        (residueSliceObject hU u0)}
    (α : ξ ⟶ η) :
    hatObj hU x hx u0 openImmersion h_factor ξ ⟶
      hatObj hU x hx u0 openImmersion h_factor η := by
  let hom :
      Fiber.fiberInclusion.obj (hatObj hU x hx u0 openImmersion h_factor η).target ⟶
        Fiber.fiberInclusion.obj (hatObj hU x hx u0 openImmersion h_factor ξ).target :=
    restrictAlong_congr x
        ((congrArg (fun i ↦ i ≫ eqToHom hx.symm) α.hom.w.symm).trans
          (Category.assoc _ _ _)) ≫
      restrictAlong_hom x (specToObj hU x hx u0 openImmersion h_factor ξ) α.hom.left
  have laws : (pFpFlatProperGroupoids S).IsHomLift
        (specOverMap openImmersion α.baseHom) hom ∧
      (hatObj hU x hx u0 openImmersion h_factor ξ).fromResidue =
        (hatObj hU x hx u0 openImmersion h_factor η).fromResidue ≫ hom := by
    sorry
  exact Predeformation.Hom.of α.baseHom hom laws.1 laws.2

/-- The morphism `hat x` of predeformation categories at the canonical
residue-field point `Spec(κ(u0)) ⟶ U`. Object map: cartesian restriction of `x`
along the `Spec(A) ⟶ U` arrow of a slice infinitesimal deformation. -/
def hat [AlgebraicGeometry.IsLocallyNoetherian S] [AlgebraicGeometry.LocallyOfFiniteType hU]
    (x : FpFlatProperGroupoids S)
    (hx : (pFpFlatProperGroupoids S).obj x = Over.mk hU) (u0 : U)
    [IsFiniteTypePoint u0] {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
          openImmersion =
        fromResidueField u0 ≫ hU) :
    AlgebraicGeometry.GroupoidsOver.Predeformation.predeformation openImmersion
        h_factor (GroupoidsOver.slice (Over.mk hU)) (residueSliceObject hU u0) ⥤ᵇ
      BasedCategory.ofFunctor
        (predeformationFunctor openImmersion (fromResidueField u0 ≫ hU) h_factor
          (residueObj hU x hx u0)) := by
  let source := AlgebraicGeometry.GroupoidsOver.Predeformation.predeformation openImmersion
    h_factor (GroupoidsOver.slice (Over.mk hU)) (residueSliceObject hU u0)
  let objMap := hatObj hU x hx u0 openImmersion h_factor
  let homMap {ξ η : source.obj} (α : ξ ⟶ η) := hatHom hU x hx u0 openImmersion h_factor α
  have laws : (∀ ξ : source.obj, homMap (𝟙 ξ) = 𝟙 (objMap ξ)) ∧
      (∀ {ξ η ζ : source.obj} (α : ξ ⟶ η) (β : η ⟶ ζ),
        homMap (α ≫ β) = homMap α ≫ homMap β) := by
    sorry
  exact { obj := objMap, map := homMap, map_id := laws.1, map_comp := laws.2, w := rfl }

/-- Applying `hat` preserves the Artinian base and sends the target to the
cartesian restriction of `x` along the stored `Spec(A) ⟶ U` arrow. -/
theorem hat_obj [AlgebraicGeometry.IsLocallyNoetherian S] [AlgebraicGeometry.LocallyOfFiniteType hU]
    (x : FpFlatProperGroupoids S)
    (hx : (pFpFlatProperGroupoids S).obj x = Over.mk hU) (u0 : U)
    [IsFiniteTypePoint u0] {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
          openImmersion =
        fromResidueField u0 ≫ hU)
    (ξ :
      AlgebraicGeometry.GroupoidsOver.Predeformation.Obj openImmersion
        (fromResidueField u0 ≫ hU) h_factor (GroupoidsOver.slice (Over.mk hU))
        (residueSliceObject hU u0)) :
    ((hat hU x hx u0 openImmersion h_factor).obj ξ).base = ξ.base ∧
      Fiber.fiberInclusion.obj
          ((hat hU x hx u0 openImmersion h_factor).obj ξ).target =
        restrictAlong x (specToObj hU x hx u0 openImmersion h_factor ξ) :=
  sorry

/-- `hat` is the based functor of cartesian restrictions of `x` along Artinian
test schemes over `U` at `κ(u0)`. -/
theorem hat_spec [AlgebraicGeometry.IsLocallyNoetherian S] [AlgebraicGeometry.LocallyOfFiniteType hU]
    (x : FpFlatProperGroupoids S)
    (hx : (pFpFlatProperGroupoids S).obj x = Over.mk hU) (u0 : U)
    [IsFiniteTypePoint u0] {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
          openImmersion =
        fromResidueField u0 ≫ hU) :
    (hat hU x hx u0 openImmersion h_factor).toFunctor ⋙
        predeformationFunctor openImmersion (fromResidueField u0 ≫ hU) h_factor
          (residueObj hU x hx u0) =
      AlgebraicGeometry.GroupoidsOver.Predeformation.forget openImmersion
        (fromResidueField u0 ≫ hU) h_factor (GroupoidsOver.slice (Over.mk hU))
        (residueSliceObject hU u0) :=
  sorry

/-- An object `x` of `Spaces'_{fp, flat, proper}` over `U` is versal at a finite
type point `u0` of `U` when the morphism `hat x` of predeformation categories at
`Spec(κ(u0)) ⟶ U` is smooth on every affine-open factorization of
`Spec(κ(u0)) ⟶ S`. -/
def IsVersalAt [AlgebraicGeometry.IsLocallyNoetherian S] [AlgebraicGeometry.LocallyOfFiniteType hU]
    (x : FpFlatProperGroupoids S)
    (hx : (pFpFlatProperGroupoids S).obj x = Over.mk hU) (u0 : U) : Prop :=
  ∀ [IsFiniteTypePoint u0] {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
          openImmersion =
        fromResidueField u0 ≫ hU),
    BasedFunctor.IsSmooth (hat hU x hx u0 openImmersion h_factor)

/-- Versality at `u0` is smoothness of the canonical residue-field `hat` on every
affine-open factorization of `Spec(κ(u0)) ⟶ S`. -/
theorem isVersalAt_iff [AlgebraicGeometry.IsLocallyNoetherian S] [AlgebraicGeometry.LocallyOfFiniteType hU]
    (x : FpFlatProperGroupoids S)
    (hx : (pFpFlatProperGroupoids S).obj x = Over.mk hU) (u0 : U)
    [IsFiniteTypePoint u0] :
    IsVersalAt hU x hx u0 ↔
      ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
        [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
        (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
        [AlgebraicGeometry.IsOpenImmersion openImmersion]
        (h_factor :
          Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
              openImmersion =
            fromResidueField u0 ≫ hU),
        BasedFunctor.IsSmooth (hat hU x hx u0 openImmersion h_factor) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids
