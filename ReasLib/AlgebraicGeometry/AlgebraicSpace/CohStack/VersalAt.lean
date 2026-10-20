module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Predeformation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt

/-!
# Versality of coherent sheaves at finite type points

The cartesian restriction of an object of `CohStack f` along a morphism of test
schemes, the induced morphism `hat` of predeformation categories at a residue
field, and the resulting versality predicate. Hom-types of `Obj f`
live in `Type (u + 1)`, so this cannot be an instance of
`AlgebraicGeometry.GroupoidsOver.IsVersalAt`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Functor
open AlgebraicGeometry.GroupoidsOver
  (residueFieldType fromResidueField residueSliceObject)
open AlgebraicGeometry.GroupoidsOver.Predeformation
  (specOver specOverMap specOver_toResidue)
open AlgebraicGeometry.AlgebraicSpace.CohStack
open scoped BasedFunctor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable (f : X ⟶ ofOver (Over.mk (𝟙 S))) [FinitePresentation f]

/-- The test scheme of the cartesian lift of `x` along a morphism of schemes over `S`. -/
def restrictAlongTest (x : Obj f) {T : Over S} (h : T ⟶ (p f).obj x) :
    SchemesOver (ofOver (Over.mk (𝟙 S))) :=
  CostructuredArrow.mk ((ofOverFunctor S).map h ≫ x.σ.hom)

/-- The cartesian morphism of test schemes from the lift of `x` along `h` to `x.σ`. -/
def restrictAlongArrow (x : Obj f) {T : Over S} (h : T ⟶ (p f).obj x) :
    restrictAlongTest f x h ⟶ x.σ :=
  CostructuredArrow.homMk' x.σ h

/-- The cartesian lift of an object of `CohStack f` along a morphism of test schemes. -/
def restrictAlong (x : Obj f) {T : Over S} (h : T ⟶ (p f).obj x) : Obj f :=
  let σ := restrictAlongTest f x h
  let pulledModule := (Modules.pullback (fiberMap f (restrictAlongArrow f x h))).obj x.module
  let laws : pulledModule.IsFinitePresentation ∧
      Modules.flatOver pulledModule (fiberToBase f σ) ∧
      Modules.HasProperSupportOver (fiberToBase f σ) pulledModule := sorry
  { σ := σ
    module := pulledModule
    isFinitePresentation := laws.1
    isFlat := laws.2.1
    hasProperSupport := laws.2.2 }

/-- The test scheme of `restrictAlong x h` is the source of `h`. -/
theorem restrictAlong_p (x : Obj f) {T : Over S} (h : T ⟶ (p f).obj x) :
    (p f).obj (restrictAlong f x h) = T :=
  sorry

/-- The module of `restrictAlong x h` is the pullback of `x.module` along the fibre map of `h`. -/
theorem restrictAlong_spec (x : Obj f) {T : Over S} (h : T ⟶ (p f).obj x) :
    (restrictAlong f x h).σ = restrictAlongTest f x h ∧
      (restrictAlong f x h).module =
        (Modules.pullback (fiberMap f (restrictAlongArrow f x h))).obj x.module :=
  sorry

/-- Functoriality of `restrictAlongTest` along a composite morphism of test schemes. -/
private theorem restrictAlongTest_map_comp (x : Obj f) {T T' : Over S} (h : T' ⟶ (p f).obj x)
    (φ : T ⟶ T') :
    restrictAlongTest f x (φ ≫ h) =
      CostructuredArrow.mk
        ((ofOverFunctor S).map φ ≫ (restrictAlongTest f x h).hom) :=
  congrArg CostructuredArrow.mk
    ((congrArg (fun i ↦ i ≫ x.σ.hom) ((ofOverFunctor S).map_comp φ h)).trans
      (Category.assoc ((ofOverFunctor S).map φ) ((ofOverFunctor S).map h) x.σ.hom))

/-- The cartesian morphism of test schemes for a composite arrow. -/
def restrictAlong_hom_base (x : Obj f) {T T' : Over S} (h : T' ⟶ (p f).obj x)
    (φ : T ⟶ T') :
    (restrictAlong f x (φ ≫ h)).σ ⟶ (restrictAlong f x h).σ :=
  eqToHom (by exact restrictAlongTest_map_comp f x h φ) ≫
    CostructuredArrow.homMk' (restrictAlong f x h).σ φ

/-- Composing the cartesian test-scheme morphism along `φ` with the lift of `h`
recovers the lift of `φ ≫ h`. -/
private theorem restrictAlong_hom_base_comp (x : Obj f) {T T' : Over S} (h : T' ⟶ (p f).obj x)
    (φ : T ⟶ T') :
    restrictAlong_hom_base f x h φ ≫ restrictAlongArrow f x h =
      restrictAlongArrow f x (φ ≫ h) :=
  (Category.assoc (eqToHom (restrictAlongTest_map_comp f x h φ))
      (CostructuredArrow.homMk' (restrictAlong f x h).σ φ)
      (restrictAlongArrow f x h)).trans
    (CostructuredArrow.homMk'_comp x.σ h φ).symm

/-- The module isomorphism witnessing that restriction along `φ ≫ h` is the
pullback of restriction along `h`. -/
def restrictAlong_hom_iso (x : Obj f) {T T' : Over S} (h : T' ⟶ (p f).obj x)
    (φ : T ⟶ T') :
    (Modules.pullback (fiberMap f (restrictAlong_hom_base f x h φ))).obj
        (restrictAlong f x h).module ≅
      (restrictAlong f x (φ ≫ h)).module :=
  (Modules.pullbackCompIso (fiberMap f (restrictAlong_hom_base f x h φ))
      (fiberMap f (restrictAlongArrow f x h))).app x.module ≪≫
    eqToIso
      (congrArg (fun ψ ↦ (Modules.pullback ψ).obj x.module)
        ((fiberMap_comp_eq f (restrictAlong_hom_base f x h φ)
            (restrictAlongArrow f x h)).symm.trans
          (congrArg (fiberMap f) (by exact restrictAlong_hom_base_comp f x h φ))))

/-- The cartesian morphism `restrictAlong x (φ ≫ h) ⟶ restrictAlong x h` in `Obj f`. -/
def restrictAlong_hom (x : Obj f) {T T' : Over S} (h : T' ⟶ (p f).obj x)
    (φ : T ⟶ T') :
    restrictAlong f x (φ ≫ h) ⟶ restrictAlong f x h where
  base := restrictAlong_hom_base f x h φ
  iso := restrictAlong_hom_iso f x h φ

/-- Transport of cartesian restrictions along an equality of test-scheme morphisms. -/
def restrictAlong_congr (x : Obj f) {T : Over S} {h₁ h₂ : T ⟶ (p f).obj x}
    (e : h₁ = h₂) : restrictAlong f x h₁ ⟶ restrictAlong f x h₂ :=
  eqToHom (congrArg (restrictAlong f x) e)

variable {U : Scheme.{u}} (hU : U ⟶ S)

/-- The morphism `Spec(κ(u0)) ⟶ U` over `S`, as an arrow into the test scheme of `x`. -/
def residueToObj (x : Obj f) (hx : (p f).obj x = Over.mk hU) (u0 : U) :
    Over.mk (fromResidueField u0 ≫ hU) ⟶ (p f).obj x :=
  (Over.homMk (fromResidueField u0) :
      Over.mk (fromResidueField u0 ≫ hU) ⟶ Over.mk hU) ≫
    eqToHom hx.symm

/-- The residue object of `x` at a point `u0`, obtained by cartesian restriction along
`Spec(κ(u0)) ⟶ U`. -/
def residueObj (x : Obj f) (hx : (p f).obj x = Over.mk hU) (u0 : U) :
    (p f).Fiber (Over.mk (fromResidueField u0 ≫ hU)) :=
  ⟨restrictAlong f x (residueToObj f hU x hx u0), rfl⟩

/-- `residueObj` is the cartesian restriction of `x` along `fromResidueField u0`. -/
theorem residueObj_spec (x : Obj f) (hx : (p f).obj x = Over.mk hU) (u0 : U) :
    Fiber.fiberInclusion.obj (residueObj f hU x hx u0) =
      restrictAlong f x (residueToObj f hU x hx u0) :=
  sorry

/-- The arrow `Spec(A) ⟶ U` over `S` carried by a slice predeformation object, as an
arrow into the test scheme of `x`. -/
def specToObj [AlgebraicGeometry.IsLocallyNoetherian S]
    (x : Obj f) (hx : (p f).obj x = Over.mk hU) (u0 : U)
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [AlgebraicGeometry.IsOpenImmersion openImmersion]
    [AlgebraicGeometry.LocallyOfFiniteType (fromResidueField u0 ≫ hU)]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
          openImmersion =
        fromResidueField u0 ≫ hU)
    (ξ :
      AlgebraicGeometry.GroupoidsOver.Predeformation.Obj openImmersion
        (fromResidueField u0 ≫ hU) h_factor (GroupoidsOver.slice (Over.mk hU))
        (residueSliceObject hU u0)) :
    (Fiber.fiberInclusion.obj ξ.target).left ⟶ (p f).obj x :=
  (Fiber.fiberInclusion.obj ξ.target).hom ≫ eqToHom hx.symm

/-- The object of `ℱ_{Coh_{X/S}, κ(u0), x0}` obtained by restricting `x` along the
Artinian test scheme of a slice predeformation object. -/
def hatObj [AlgebraicGeometry.IsLocallyNoetherian S]
    (x : Obj f) (hx : (p f).obj x = Over.mk hU) (u0 : U)
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [AlgebraicGeometry.IsOpenImmersion openImmersion]
    [AlgebraicGeometry.LocallyOfFiniteType (fromResidueField u0 ≫ hU)]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
          openImmersion =
        fromResidueField u0 ≫ hU)
    (ξ :
      AlgebraicGeometry.GroupoidsOver.Predeformation.Obj openImmersion
        (fromResidueField u0 ≫ hU) h_factor (GroupoidsOver.slice (Over.mk hU))
        (residueSliceObject hU u0)) :
    Predeformation.Obj f openImmersion (fromResidueField u0 ≫ hU) h_factor
      (residueObj f hU x hx u0) where
  base := ξ.base
  target := ⟨restrictAlong f x (specToObj f hU x hx u0 openImmersion h_factor ξ),
    (restrictAlong_p f x (specToObj f hU x hx u0 openImmersion h_factor ξ)).trans
      ξ.target.property⟩
  fromResidue :=
    restrictAlong_congr f x
        ((congrArg (fun i ↦ i ≫ eqToHom hx.symm) ξ.fromResidue.w.symm).trans
          (Category.assoc _ _ _)) ≫
      restrictAlong_hom f x (specToObj f hU x hx u0 openImmersion h_factor ξ)
        ξ.fromResidue.left
  over_fromResidue := sorry

/-- The reversed arrow in `CohStack f` induced by a morphism of slice predeformation
categories. -/
def hatHom [AlgebraicGeometry.IsLocallyNoetherian S]
    (x : Obj f) (hx : (p f).obj x = Over.mk hU) (u0 : U)
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [AlgebraicGeometry.IsOpenImmersion openImmersion]
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
    hatObj f hU x hx u0 openImmersion h_factor ξ ⟶
      hatObj f hU x hx u0 openImmersion h_factor η :=
  let hom :=
    restrictAlong_congr f x
        ((congrArg (fun i ↦ i ≫ eqToHom hx.symm) α.hom.w.symm).trans
          (Category.assoc _ _ _)) ≫
      restrictAlong_hom f x (specToObj f hU x hx u0 openImmersion h_factor ξ)
        α.hom.left
  let laws : (p f).IsHomLift (specOverMap openImmersion α.baseHom) hom ∧
      (hatObj f hU x hx u0 openImmersion h_factor ξ).fromResidue =
        (hatObj f hU x hx u0 openImmersion h_factor η).fromResidue ≫ hom := sorry
  { baseHom := α.baseHom
    hom := hom
    over_hom := laws.1
    triangle := laws.2 }

/-- The functor sending an infinitesimal deformation over `U` to the cartesian
restriction of `x` along its Artinian test scheme. -/
def hatFunctor [AlgebraicGeometry.IsLocallyNoetherian S] [AlgebraicGeometry.LocallyOfFiniteType hU] (x : Obj f)
    (hx : (p f).obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
          openImmersion =
        fromResidueField u0 ≫ hU) :
    AlgebraicGeometry.GroupoidsOver.Predeformation.Obj openImmersion
        (fromResidueField u0 ≫ hU) h_factor (GroupoidsOver.slice (Over.mk hU))
        (residueSliceObject hU u0) ⥤
      Predeformation.Obj f openImmersion (fromResidueField u0 ≫ hU) h_factor
        (residueObj f hU x hx u0) :=
  let obj := hatObj f hU x hx u0 openImmersion h_factor
  let map := fun {ξ η} (α : ξ ⟶ η) => hatHom f hU x hx u0 openImmersion h_factor α
  let laws :
      (∀ ξ, map (𝟙 ξ) = 𝟙 (obj ξ)) ∧
      (∀ {ξ η ζ} (α : ξ ⟶ η) (β : η ⟶ ζ), map (α ≫ β) = map α ≫ map β) := sorry
  { obj := obj
    map := map
    map_id := laws.1
    map_comp := laws.2 }

/-- The morphism `hat x` of predeformation categories at the canonical residue-field
point `Spec(κ(u0)) ⟶ U`. Object map: cartesian restriction of `x` along the
`Spec(A) ⟶ U` arrow of a slice infinitesimal deformation. -/
def hat [AlgebraicGeometry.IsLocallyNoetherian S] [AlgebraicGeometry.LocallyOfFiniteType hU] (x : Obj f)
    (hx : (p f).obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
          openImmersion =
        fromResidueField u0 ≫ hU) :
    AlgebraicGeometry.GroupoidsOver.Predeformation.predeformation openImmersion h_factor
        (GroupoidsOver.slice (Over.mk hU)) (residueSliceObject hU u0) ⥤ᵇ
      BasedCategory.ofFunctor
        (predeformation f openImmersion (fromResidueField u0 ≫ hU) h_factor
          (residueObj f hU x hx u0)) where
  toFunctor := hatFunctor f hU x hx u0 openImmersion h_factor
  w := sorry

/-- Applying `hat` preserves the Artinian base and sends the target to the cartesian
restriction of `x` along the stored `Spec(A) ⟶ U` arrow. -/
theorem hat_obj [AlgebraicGeometry.IsLocallyNoetherian S] [AlgebraicGeometry.LocallyOfFiniteType hU] (x : Obj f)
    (hx : (p f).obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
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
    ((hat f hU x hx u0 openImmersion h_factor).obj ξ).base = ξ.base ∧
      Fiber.fiberInclusion.obj ((hat f hU x hx u0 openImmersion h_factor).obj ξ).target =
        restrictAlong f x (specToObj f hU x hx u0 openImmersion h_factor ξ) :=
  sorry

/-- `hat` is the based functor of cartesian restrictions of `x` along Artinian test
schemes over `U` at `κ(u0)`. -/
theorem hat_spec [AlgebraicGeometry.IsLocallyNoetherian S] [AlgebraicGeometry.LocallyOfFiniteType hU] (x : Obj f)
    (hx : (p f).obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
          openImmersion =
        fromResidueField u0 ≫ hU) :
    (hat f hU x hx u0 openImmersion h_factor).toFunctor ⋙
        predeformation f openImmersion (fromResidueField u0 ≫ hU) h_factor
          (residueObj f hU x hx u0) =
      AlgebraicGeometry.GroupoidsOver.Predeformation.forget openImmersion
        (fromResidueField u0 ≫ hU) h_factor (GroupoidsOver.slice (Over.mk hU))
        (residueSliceObject hU u0) :=
  sorry

/-- An object `x` of `CohStack f` over `U` is versal at a finite type point `u0` of
`U` when the morphism `hat x` of predeformation categories at
`Spec(κ(u0)) ⟶ U` is smooth on every affine-open factorization of
`Spec(κ(u0)) ⟶ S`. -/
def IsVersalAt [AlgebraicGeometry.IsLocallyNoetherian S] [AlgebraicGeometry.LocallyOfFiniteType hU] (x : Obj f)
    (hx : (p f).obj x = Over.mk hU) (u0 : U) : Prop :=
  ∀ [IsFiniteTypePoint u0] {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
          openImmersion =
        fromResidueField u0 ≫ hU),
    BasedFunctor.IsSmooth (hat f hU x hx u0 openImmersion h_factor)

/-- Versality at `u0` is smoothness of the canonical residue-field `hat` on every
affine-open factorization of `Spec(κ(u0)) ⟶ S`. -/
theorem isVersalAt_iff [AlgebraicGeometry.IsLocallyNoetherian S] [AlgebraicGeometry.LocallyOfFiniteType hU] (x : Obj f)
    (hx : (p f).obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0] :
    IsVersalAt f hU x hx u0 ↔
      ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
        [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
        (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
        [AlgebraicGeometry.IsOpenImmersion openImmersion]
        (h_factor :
          Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
              openImmersion =
            fromResidueField u0 ≫ hU),
        BasedFunctor.IsSmooth (hat f hU x hx u0 openImmersion h_factor) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
