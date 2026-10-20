module

public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Sites.Whiskering
public import stacks_project.Chap91.Lemma_91_14_2_Translate
public import stacks_project.Chap91.Lemma_91_14_2_KernelBridge
public import stacks_project.Chap91.Lemma_91_14_2_UniversalDerivation
public import stacks_project.Chap76.Lemma_76_9_2

/-!
# Isomorphism classes of flat first-order algebraic-space lifts

Two flat lifts are isomorphic when there is an ambient isomorphism over `Y'`
reducing to the identity on `X`. Their classes form a principal homogeneous
space under Ext¹(NL[X/Y], f^* 𝒞_{Y/Y'}), via pushout translation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension
open AlgebraicGeometry.AlgebraicSpace.Thickening
open scoped AlgebraicGeometry.AlgebraicSpace DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Thickening
namespace FlatLift

variable {S : Scheme.{u}} {Y Y' X : AlgebraicSpace S}
variable {t : Y ⟶ Y'} [IsFirstOrderThickening t] {f : X ⟶ Y} [Flat f]

/-- The setoid identifying flat lifts that admit an ambient isomorphism over `Y'`
reducing to the identity on `X`. -/
def isoSetoid (t : Y ⟶ Y') [IsFirstOrderThickening t] (f : X ⟶ Y) [Flat f] :
    Setoid (FlatLift t f) where
  r L₁ L₂ := Nonempty (Hom L₁ L₂)
  iseqv := sorry

/-- Two flat lifts are related iff they admit a morphism of lifts. -/
theorem isoSetoid_rel (L₁ L₂ : FlatLift t f) :
    isoSetoid t f L₁ L₂ ↔ Nonempty (Hom L₁ L₂) := sorry

/-- Isomorphism classes of flat first-order lifts of `f` across `t`. -/
abbrev IsoClass (t : Y ⟶ Y') [IsFirstOrderThickening t] (f : X ⟶ Y) [Flat f] :=
  Quotient (isoSetoid t f)

/-- The isomorphism class of a given flat lift. -/
def isoClassMk (L : FlatLift t f) : IsoClass t f :=
  Quotient.mk (isoSetoid t f) L

/-- A morphism of flat lifts identifies isomorphism classes. -/
theorem isoClassMk_eq_mk_of_hom {L₁ L₂ : FlatLift t f} (φ : Hom L₁ L₂) :
    isoClassMk L₁ = isoClassMk L₂ := sorry

/-- The obstruction class in Ext¹(NL[f], f^* 𝒞_{Y/Y'}) comparing two flat lifts.
It is a class `ξ` for which `translate ξ L₁` realizes `L₂`. The algebra-difference
representative is recorded by `exists_algebraDiff` / `liftObstruction` in the
Translate module. -/
def obstruction (L₁ L₂ : FlatLift t f) : extOneNL t f :=
  liftObstruction L₁ L₂

/-- `obstruction L₁ L₂` translates `L₁` onto `L₂`. -/
theorem obstruction_spec (L₁ L₂ : FlatLift t f) :
    Nonempty (Hom (translate (obstruction L₁ L₂) L₁) L₂) := sorry

/-- Translating a lift by ξ realizes ξ as an obstruction. -/
theorem obstruction_translate (ξ : extOneNL t f) (L : FlatLift t f) :
    obstruction L (translate ξ L) = ξ := sorry

/-- The obstruction vanishes iff the two lifts admit a morphism of lifts. -/
theorem obstruction_eq_zero_iff (L₁ L₂ : FlatLift t f) :
    obstruction L₁ L₂ = 0 ↔ Nonempty (Hom L₁ L₂) := sorry

/-- Action of an Ext¹ class on an isomorphism class, via `translate`. -/
def vadd (ξ : extOneNL t f) (p : IsoClass t f) : IsoClass t f :=
  Quotient.map (translate ξ) sorry p

/-- Difference of isomorphism classes, as an Ext¹ class. Subtraction is oriented
so that `[X'_ξ] -ᵥ [X'] = ξ` when `o(X', X'_ξ) = ξ`. -/
def vsub (p q : IsoClass t f) : extOneNL t f :=
  Quotient.lift₂ (fun L₁ L₂ ↦ obstruction L₂ L₁) sorry p q

/-- Ext¹ classes act on isomorphism classes of flat lifts by translation. -/
instance instVAdd_isoClass : VAdd (extOneNL t f) (IsoClass t f) where
  vadd := vadd

/-- Difference of isomorphism classes of flat lifts is an Ext¹ class. -/
instance instVSub_isoClass : VSub (extOneNL t f) (IsoClass t f) where
  vsub := vsub

/-- The Ext¹-action of naive cotangent classes on isomorphism classes of flat
lifts. -/
instance instAddAction_isoClass : AddAction (extOneNL t f) (IsoClass t f) where
  add_vadd := sorry
  zero_vadd := sorry

/-- The Ext¹-action computes on representatives by `translate`. -/
theorem vadd_mk (ξ : extOneNL t f) (L : FlatLift t f) :
    ξ +ᵥ isoClassMk L = isoClassMk (translate ξ L) := sorry

/-- Torsor subtraction computes on representatives by the reversed obstruction. -/
theorem vsub_mk (L₁ L₂ : FlatLift t f) :
    isoClassMk L₁ -ᵥ isoClassMk L₂ = obstruction L₂ L₁ := sorry

/-- The zero Ext¹ class acts as the identity on isomorphism classes. -/
theorem vadd_zero (p : IsoClass t f) :
    (0 : extOneNL t f) +ᵥ p = p := sorry

/-- The Ext¹-action is compatible with addition. -/
theorem add_vadd (ξ η : extOneNL t f) (p : IsoClass t f) :
    (ξ + η) +ᵥ p = ξ +ᵥ η +ᵥ p := sorry

/-- With a chosen flat lift as basepoint, isomorphism classes are an additive
torsor under Ext¹(NL[f], f^* 𝒞_{Y/Y'}). -/
@[reducible]
def addTorsor (S0 : FlatLift t f) : AddTorsor (extOneNL t f) (IsoClass t f) where
  nonempty := ⟨isoClassMk S0⟩
  vsub_vadd' := sorry
  vadd_vsub' := sorry

/-- A basepoint lift makes the set of isomorphism classes nonempty. -/
theorem addTorsor_nonempty (S0 : FlatLift t f) : Nonempty (IsoClass t f) := sorry

/-- The identity filling of the identity cube has commuting square `L.i ≫ 𝟙 = 𝟙 ≫ L.i`. -/
theorem id_comm_thickening (L : FlatLift t f) :
    L.i ≫ 𝟙 L.space = 𝟙 X ≫ L.i := sorry

/-- The identity algebra map of a flat lift, as `(𝟙_{X'})^♯` on `X_spaces,étale`. -/
def idAlgebraMap (L : FlatLift t f) :
    inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i :=
  structureMap_transported L.i L.i (𝟙 X) (𝟙 L.space) (id_comm_thickening L)

/-- A reducing-to-identity automorphism fills the identity cube. -/
theorem autoAlgebraMap_comm_thickening {L : FlatLift t f} (φ : ReduceIdAuto L) :
    L.i ≫ φ.hom = 𝟙 X ≫ L.i := sorry

/-- Identity-cube algebra map of a reducing-to-identity automorphism. -/
def autoAlgebraMap {L : FlatLift t f} (φ : ReduceIdAuto L) :
    inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i :=
  structureMap_transported L.i L.i (𝟙 X) φ.hom (autoAlgebraMap_comm_thickening φ)

/-- The identity filling commutes with the structure-sheaf square. -/
theorem idAlgebraMap_commutes (L : FlatLift t f) :
    structureMap_commutes L.i L.i (𝟙 X) (idAlgebraMap L) := sorry

/-- The identity filling is an `𝒪_{Y'}`-algebra map. -/
theorem idAlgebraMap_isAlgebra (L : FlatLift t f) :
    isAlgebraOverBase (L.i ≫ L.f') L.f' (L.i ≫ L.f') L.f'
      L.i L.i (𝟙 X) rfl rfl (Category.id_comp (L.i ≫ L.f')) (idAlgebraMap L) :=
  sorry

/-- The identity-cube algebra map of a reducing-to-identity automorphism commutes
with the structure-sheaf square. -/
theorem autoAlgebraMap_commutes {L : FlatLift t f} (φ : ReduceIdAuto L) :
    structureMap_commutes L.i L.i (𝟙 X) (autoAlgebraMap φ) := sorry

/-- The identity-cube algebra map of a reducing-to-identity automorphism is an
`𝒪_{Y'}`-algebra map. -/
theorem autoAlgebraMap_isAlgebra {L : FlatLift t f} (φ : ReduceIdAuto L) :
    isAlgebraOverBase (L.i ≫ L.f') L.f' (L.i ≫ L.f') L.f'
      L.i L.i (𝟙 X) rfl rfl (Category.id_comp (L.i ≫ L.f')) (autoAlgebraMap φ) :=
  sorry

/-- Forget ring-valued sheaves on the spaces-étale site to abelian groups. -/
abbrev forgetSpacesRing (X : AlgebraicSpace S) :
    Sheaf (spacesEtaleTopology X) RingCat.{u} ⥤
      Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u} :=
  sheafCompose (spacesEtaleTopology X) (forget₂ RingCat AddCommGrpCat.{u})

/-- Restriction of abelian sheaves from `X_spaces,étale` to `X_étale`. -/
abbrev restrictSpacesAdd (X : AlgebraicSpace S) :
    Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u} ⥤
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u} :=
  (smallEtaleToSpaces X).sheafPushforwardContinuous AddCommGrpCat.{u}
    (smallEtaleTopology X) (spacesEtaleTopology X)

/-- The Kähler object `Ω[f]` as the cokernel of the naive cotangent differential. -/
abbrev omegaSheaf (f : X ⟶ Y) : X.Modules :=
  cokernel (cotangentDifferential f)

/-- Maps `Ω[f] ⟶ f^* 𝒞_{Y/Y'}`, the underived Hom identifying Ext⁰. -/
abbrev homOmega (t : Y ⟶ Y') [IsFirstOrderThickening t] (f : X ⟶ Y) :=
  omegaSheaf f ⟶ pulledConormal t f

/-- Canonical map `Ω[f] ⟶ H⁰(NL[f])` through cycles in degree `0`. -/
def omegaToHomology (f : X ⟶ Y) :
    omegaSheaf f ⟶
      (HomologicalComplex.homologyFunctor (Modules X) (ComplexShape.up ℤ) (0 : ℤ)).obj
        NL[f] :=
  cokernel.desc (cotangentDifferential f)
    ((NL[f]).liftCycles (𝟙 ((NL[f]).X 0)) ((ComplexShape.up ℤ).next 0) rfl sorry ≫
      (NL[f]).homologyπ 0) sorry

/-- Canonical augmentation `NL[f] ⟶ Ω[f][0]`. -/
def nlAugmentation :
    NL[f] ⟶ (CochainComplex.singleFunctor (Modules X) 0).obj (omegaSheaf f) :=
  HomologicalComplex.mkHomToSingle (cokernel.π (cotangentDifferential f))
    (fun i hi ↦ sorry)

/-- Ext⁰ class of a map `Ω[f] ⟶ f^* 𝒞`. -/
def homOmegaToExtZero (α : homOmega t f) : extZeroNL t f :=
  (CategoryTheory.ShiftedHom.homEquiv (0 : ℤ) rfl)
    (DerivedCategory.Q.map
      (nlAugmentation ≫
        (CochainComplex.singleFunctor (Modules X) 0).map α))

/-- `homOmegaToExtZero` is `Q.map` of the augmentation followed by the degree-zero single of `α`. -/
theorem homOmegaToExtZero_apply (α : homOmega t f) :
    homOmegaToExtZero α =
      (CategoryTheory.ShiftedHom.homEquiv (0 : ℤ) rfl)
        (DerivedCategory.Q.map
          (nlAugmentation ≫
            (CochainComplex.singleFunctor (Modules X) 0).map α)) := sorry

/-- The identification `Hom(Ω[f], f^* 𝒞) ≃ Ext⁰(Q NL[f], Q((f^* 𝒞)[0]))`. -/
theorem homOmegaToExtZero_bijective :
    Function.Bijective (fun α : homOmega t f ↦ homOmegaToExtZero α) := sorry

/-- Inverse of `homOmegaToExtZero`: unshift the Ext⁰ class, pass to `H⁰`, and
identify `H⁰((f^* 𝒞)[0])` with `f^* 𝒞`. -/
def extZeroToHomOmega (ξ : extZeroNL t f) : homOmega t f :=
  omegaToHomology f ≫
    (DerivedCategory.homologyFunctorFactors (Modules X) (0 : ℤ)).inv.app NL[f] ≫
    (DerivedCategory.homologyFunctor (Modules X) (0 : ℤ)).map
      ((CategoryTheory.ShiftedHom.homEquiv (0 : ℤ) rfl).symm ξ) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules X) (0 : ℤ)).hom.app
      (pulledConormal t f)

/-- `extZeroToHomOmega` inverts `homOmegaToExtZero`. -/
theorem extZeroToHomOmega_left_inv (α : homOmega t f) :
    extZeroToHomOmega (homOmegaToExtZero α) = α := sorry

/-- `homOmegaToExtZero` inverts `extZeroToHomOmega`. -/
theorem extZeroToHomOmega_right_inv (ξ : extZeroNL t f) :
    homOmegaToExtZero (extZeroToHomOmega ξ) = ξ := sorry

/-- Zero Ext⁰ corresponds to the zero map `Ω[f] ⟶ f^* 𝒞`. -/
theorem extZeroToHomOmega_zero :
    extZeroToHomOmega (0 : extZeroNL t f) = 0 := sorry

/-- The inverse-image form of `α - (𝟙_{X'})^♯` on `X_spaces,étale`. -/
def algebraMapAddDiff {L : FlatLift t f}
    (α : inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i) :
    (forgetSpacesRing X).obj (inverseImageClosedStructureSheaf (𝟙 X) L.i) ⟶
      (forgetSpacesRing X).obj (closedStructureSheaf L.i) :=
  (forgetSpacesRing X).map α - (forgetSpacesRing X).map (idAlgebraMap L)

/-- `algebraMapAddDiff` is the additive difference of `α` and the identity filling. -/
theorem algebraMapAddDiff_eq {L : FlatLift t f}
    (α : inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i) :
    algebraMapAddDiff α =
      (forgetSpacesRing X).map α - (forgetSpacesRing X).map (idAlgebraMap L) :=
  rfl

/-- Factorization of `α - id` through `Ker(i^♯)`. -/
def algebraMapDiffKernel {L : FlatLift t f}
    (α : inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i)
    (hα : structureMap_commutes L.i L.i (𝟙 X) α) :
    (forgetSpacesRing X).obj (inverseImageClosedStructureSheaf (𝟙 X) L.i) ⟶
      kernel ((forgetSpacesRing X).map (closedStructureSheaf_structureMap L.i)) :=
  kernel.lift ((forgetSpacesRing X).map (closedStructureSheaf_structureMap L.i))
    (algebraMapAddDiff α) sorry

/-- `algebraMapDiffKernel` is the kernel lift of `algebraMapAddDiff`. -/
theorem algebraMapDiffKernel_eq {L : FlatLift t f}
    (α : inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i)
    (hα : structureMap_commutes L.i L.i (𝟙 X) α) :
    algebraMapDiffKernel α hα ≫
      kernel.ι ((forgetSpacesRing X).map (closedStructureSheaf_structureMap L.i)) =
      algebraMapAddDiff α :=
  sorry

/-- Underlying additive sheaf of an `𝒪_X`-module on `X_étale`. -/
abbrev modulesToAdd (F : X.Modules) :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (structureSheaf X)).obj F

/-- `modulesToAdd F` is the underlying additive sheaf of `F`. -/
theorem modulesToAdd_eq (F : X.Modules) :
    modulesToAdd F = (SheafOfModules.toSheaf (structureSheaf X)).obj F :=
  rfl

/-- Restriction of `Ker(i^♯)` from `X_spaces,étale` to `X_étale`. -/
abbrev restrictedKernel (L : FlatLift t f) :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u} :=
  (restrictSpacesAdd X).obj
    (kernel ((forgetSpacesRing X).map (closedStructureSheaf_structureMap L.i)))

/-- `restrictedKernel L` is the small-étale restriction of `Ker(i^♯)`. -/
theorem restrictedKernel_eq (L : FlatLift t f) :
    restrictedKernel L =
      (restrictSpacesAdd X).obj
        (kernel ((forgetSpacesRing X).map (closedStructureSheaf_structureMap L.i))) :=
  rfl

/-- The first-order cartesian identification `Ker(i^♯)|_{X_étale} ≅ f^* 𝒞_{Y/Y'}`. -/
theorem exists_restrictedKernelIso (L : FlatLift t f) :
    Nonempty (restrictedKernel L ≅ modulesToAdd (pulledConormal t f)) := ⟨CanonicalKernel.iso L⟩

/-- Canonical isomorphism `Ker(i^♯)|_{X_étale} ≅ f^* 𝒞_{Y/Y'}` as additive sheaves. -/
def restrictedKernelIso (L : FlatLift t f) :
    restrictedKernel L ≅ modulesToAdd (pulledConormal t f) :=
  CanonicalKernel.iso L

/-- The inverse kernel identification recovers the fixed geometric ideal inclusion. -/
theorem restrictedKernelIso_spec (L : FlatLift t f) :
    (restrictedKernelIso L).inv ≫
      (restrictSpacesAdd X).map (kernel.ι (CanonicalKernel.projection L)) =
        CanonicalKernel.inclusion L :=
  CanonicalKernel.comparison_fac L

/-- The identity-cube universal derivation `i^{-1} 𝒪_{X'} ⟶ Ω[f]` on `X_étale`. -/
def structureDerivation (L : FlatLift t f) :
    (restrictSpacesAdd X).obj
        ((forgetSpacesRing X).obj (inverseImageClosedStructureSheaf (𝟙 X) L.i)) ⟶
      modulesToAdd (omegaSheaf f) :=
  (restrictSpacesAdd X).map ((forgetSpacesRing X).map
      (idAlgebraMap L ≫ closedStructureSheaf_structureMap L.i)) ≫
    (Hom.Deformation.restrictForgetRingIso X (spacesStructureSheaf X)).hom ≫
    (sheafCompose (smallEtaleTopology X) (forget₂ RingCat AddCommGrpCat.{u})).map
      ((EtaleRingedTopos.ringExtensionRestrictionIso X).hom.app (structureSheaf X)) ≫
    Hom.Deformation.derivationAdditiveMap f (omegaSheaf f) (Hom.GeometricNL.universalDerivation f)

/-- Postcomposition with `structureDerivation L` is injective on `Hom(Ω[f], f^* 𝒞)`. -/
theorem structureDerivation_injective (L : FlatLift t f) :
    Function.Injective
      (fun θ : homOmega t f ↦
        structureDerivation L ≫
          (SheafOfModules.toSheaf (structureSheaf X)).map θ) := sorry

/-- Existence of the identity-cube Kähler derivation `i^{-1} 𝒪_{X'} ⟶ Ω[f]`. -/
theorem exists_structureDerivation (L : FlatLift t f) :
    ∃ d :
      (restrictSpacesAdd X).obj
          ((forgetSpacesRing X).obj (inverseImageClosedStructureSheaf (𝟙 X) L.i)) ⟶
        modulesToAdd (omegaSheaf f),
      Function.Injective
        (fun θ : homOmega t f ↦
          d ≫ (SheafOfModules.toSheaf (structureSheaf X)).map θ) :=
  ⟨structureDerivation L, structureDerivation_injective L⟩

/-- `θ : Ω[f] ⟶ f^* 𝒞` classifies the identity-cube difference `α - id` when it
recovers that difference under `Ker(i^♯) ≅ f^* 𝒞`. -/
def classifiesDifference {L : FlatLift t f}
    (α : inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i)
    (hα : structureMap_commutes L.i L.i (𝟙 X) α) (θ : homOmega t f) : Prop :=
  structureDerivation L ≫ (SheafOfModules.toSheaf (structureSheaf X)).map θ =
    (restrictSpacesAdd X).map (algebraMapDiffKernel α hα) ≫
      (restrictedKernelIso L).hom

/-- Unfolding of `classifiesDifference`. -/
theorem classifiesDifference_iff {L : FlatLift t f}
    (α : inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i)
    (hα : structureMap_commutes L.i L.i (𝟙 X) α) (θ : homOmega t f) :
    classifiesDifference α hα θ ↔
      structureDerivation L ≫ (SheafOfModules.toSheaf (structureSheaf X)).map θ =
        (restrictSpacesAdd X).map (algebraMapDiffKernel α hα) ≫
          (restrictedKernelIso L).hom := sorry

/-- Unique factorization of `α - id` through `Ω[f]`. -/
theorem existsUnique_derivationOfAlgebraMap {L : FlatLift t f}
    (α : inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i)
    (hα : structureMap_commutes L.i L.i (𝟙 X) α)
    (halg : isAlgebraOverBase (L.i ≫ L.f') L.f' (L.i ≫ L.f') L.f'
      L.i L.i (𝟙 X) rfl rfl (Category.id_comp (L.i ≫ L.f')) α) :
    ExistsUnique fun θ : homOmega t f ↦ classifiesDifference α hα θ :=
  sorry

/-- The identity-cube derivation of an algebra map `α`, as the unique map
`Ω[f] ⟶ f^* 𝒞` classifying `α - id` under `Ker(i^♯) ≅ f^* 𝒞`. -/
def derivationOfAlgebraMap {L : FlatLift t f}
    (α : inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i)
    (hα : structureMap_commutes L.i L.i (𝟙 X) α)
    (halg : isAlgebraOverBase (L.i ≫ L.f') L.f' (L.i ≫ L.f') L.f'
      L.i L.i (𝟙 X) rfl rfl (Category.id_comp (L.i ≫ L.f')) α) :
    homOmega t f :=
  Classical.choose (existsUnique_derivationOfAlgebraMap α hα halg)

/-- `derivationOfAlgebraMap α` vanishes iff `α` is the identity filling. -/
theorem derivationOfAlgebraMap_spec {L : FlatLift t f}
    (α : inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i)
    (hα : structureMap_commutes L.i L.i (𝟙 X) α)
    (halg : isAlgebraOverBase (L.i ≫ L.f') L.f' (L.i ≫ L.f') L.f'
      L.i L.i (𝟙 X) rfl rfl (Category.id_comp (L.i ≫ L.f')) α) :
    derivationOfAlgebraMap α hα halg = 0 ↔ α = idAlgebraMap L := sorry

/-- The Ext⁰ class of an identity-cube algebra map, via `Hom(Ω[f], f^* 𝒞) ≃ Ext⁰`. -/
def extZeroOfAlgebraMap {L : FlatLift t f}
    (α : inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i)
    (hα : structureMap_commutes L.i L.i (𝟙 X) α)
    (halg : isAlgebraOverBase (L.i ≫ L.f') L.f' (L.i ≫ L.f') L.f'
      L.i L.i (𝟙 X) rfl rfl (Category.id_comp (L.i ≫ L.f')) α) :
    extZeroNL t f :=
  homOmegaToExtZero (derivationOfAlgebraMap α hα halg)

/-- `extZeroOfAlgebraMap` is `homOmegaToExtZero` of the identity-cube derivation of `α`. -/
theorem extZeroOfAlgebraMap_spec {L : FlatLift t f}
    (α : inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i)
    (hα : structureMap_commutes L.i L.i (𝟙 X) α)
    (halg : isAlgebraOverBase (L.i ≫ L.f') L.f' (L.i ≫ L.f') L.f'
      L.i L.i (𝟙 X) rfl rfl (Category.id_comp (L.i ≫ L.f')) α) :
    extZeroOfAlgebraMap α hα halg =
      homOmegaToExtZero (derivationOfAlgebraMap α hα halg) := sorry

/-- The identity filling has vanishing Ext⁰ class. -/
theorem extZeroOfAlgebraMap_id (L : FlatLift t f) :
    extZeroOfAlgebraMap (idAlgebraMap L) (idAlgebraMap_commutes L)
      (idAlgebraMap_isAlgebra L) = 0 := sorry

/-- Unique identity-cube algebra map whose derivation is the Hom(Ω, f^* 𝒞)
representative of an Ext⁰ class. -/
theorem existsUnique_perturbAlgebraMap (L : FlatLift t f) (ξ : extZeroNL t f) :
    ExistsUnique fun α :
        inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i ↦
      ∃ (hα : structureMap_commutes L.i L.i (𝟙 X) α)
        (halg : isAlgebraOverBase (L.i ≫ L.f') L.f' (L.i ≫ L.f') L.f'
          L.i L.i (𝟙 X) rfl rfl (Category.id_comp (L.i ≫ L.f')) α),
          derivationOfAlgebraMap α hα halg = extZeroToHomOmega ξ :=
  sorry

/-- The identity-cube perturbation of `(𝟙_{X'})^♯` by an Ext⁰ class, as the unique
`𝒪_{Y'}`-algebra map whose derivation is `extZeroToHomOmega ξ`. -/
def perturbAlgebraMap (L : FlatLift t f) (ξ : extZeroNL t f) :
    inverseImageClosedStructureSheaf (𝟙 X) L.i ⟶ closedStructureSheaf L.i :=
  Classical.choose (existsUnique_perturbAlgebraMap L ξ)

/-- `perturbAlgebraMap L ξ` commutes with the structure-sheaf square. -/
theorem perturbAlgebraMap_commutes (L : FlatLift t f) (ξ : extZeroNL t f) :
    structureMap_commutes L.i L.i (𝟙 X) (perturbAlgebraMap L ξ) := sorry

/-- `perturbAlgebraMap L ξ` is a morphism of `𝒪_{Y'}`-algebras. -/
theorem perturbAlgebraMap_isAlgebra (L : FlatLift t f) (ξ : extZeroNL t f) :
    isAlgebraOverBase (L.i ≫ L.f') L.f' (L.i ≫ L.f') L.f'
      L.i L.i (𝟙 X) rfl rfl (Category.id_comp (L.i ≫ L.f'))
      (perturbAlgebraMap L ξ) :=
  sorry

/-- `perturbAlgebraMap L ξ` commutes with the structure-sheaf square, is an
`𝒪_{Y'}`-algebra map, and has Ext⁰ class `ξ`. -/
theorem perturbAlgebraMap_spec (L : FlatLift t f) (ξ : extZeroNL t f) :
    structureMap_commutes L.i L.i (𝟙 X) (perturbAlgebraMap L ξ) ∧
      isAlgebraOverBase (L.i ≫ L.f') L.f' (L.i ≫ L.f') L.f'
          L.i L.i (𝟙 X) rfl rfl (Category.id_comp (L.i ≫ L.f'))
          (perturbAlgebraMap L ξ) ∧
        extZeroOfAlgebraMap (perturbAlgebraMap L ξ)
            (perturbAlgebraMap_commutes L ξ)
            (perturbAlgebraMap_isAlgebra L ξ) = ξ :=
  sorry

/-- The zero Ext⁰ class perturbs the identity filling by the identity algebra map. -/
theorem perturbAlgebraMap_zero (L : FlatLift t f) :
    perturbAlgebraMap L 0 = idAlgebraMap L := sorry

/-- The unique morphism of thickenings over `Y'` lifting the identity-cube perturbation,
by lemma 76.9.2. -/
def ofExtZeroHom (L : FlatLift t f) (ξ : extZeroNL t f) : L.space ⟶ L.space :=
  Classical.choose
    (existsUnique_hom_of_algebraMap
      (L.i ≫ L.f') L.f' (L.i ≫ L.f') L.f' L.i L.i (𝟙 X)
      rfl rfl (Category.id_comp (L.i ≫ L.f')) (perturbAlgebraMap L ξ)
      (perturbAlgebraMap_spec L ξ).1 (perturbAlgebraMap_isAlgebra L ξ))

/-- `ofExtZeroHom L ξ` is over `Y'`. -/
theorem ofExtZeroHom_over (L : FlatLift t f) (ξ : extZeroNL t f) :
    ofExtZeroHom L ξ ≫ L.f' = L.f' := sorry

/-- `ofExtZeroHom L ξ` reduces to the identity on `X`. -/
theorem ofExtZeroHom_restrict (L : FlatLift t f) (ξ : extZeroNL t f) :
    L.i ≫ ofExtZeroHom L ξ = L.i := sorry

/-- `ofExtZeroHom L ξ` is an isomorphism. -/
instance instIsIso_ofExtZeroHom (L : FlatLift t f) (ξ : extZeroNL t f) :
    IsIso (ofExtZeroHom L ξ) := sorry

/-- The Ext⁰-action on reducing-to-identity automorphisms, via identity-cube
perturbation and 76.9.2. -/
def ofExtZero (L : FlatLift t f) (ξ : extZeroNL t f) : ReduceIdAuto L :=
  ReduceIdAuto.of (ofExtZeroHom L ξ) (ofExtZeroHom_over L ξ) (ofExtZeroHom_restrict L ξ)

/-- `ofExtZero L ξ` is the 76.9.2 lift of the identity-cube perturbation of `ξ`. -/
theorem ofExtZero_spec (L : FlatLift t f) (ξ : extZeroNL t f) :
    (ofExtZero L ξ).hom = ofExtZeroHom L ξ ∧
      IsHom L.f' L.f' L.i L.i (𝟙 X) (perturbAlgebraMap L ξ) (ofExtZeroHom L ξ) ∧
        extZeroOfAlgebraMap (perturbAlgebraMap L ξ)
            (perturbAlgebraMap_commutes L ξ)
            (perturbAlgebraMap_isAlgebra L ξ) = ξ :=
  sorry

/-- The Ext⁰ class of a reducing-to-identity automorphism, as the Ext class of its
identity-cube algebra map. -/
def toExtZero {L : FlatLift t f} (φ : ReduceIdAuto L) : extZeroNL t f :=
  extZeroOfAlgebraMap (autoAlgebraMap φ) (autoAlgebraMap_commutes φ)
    (autoAlgebraMap_isAlgebra φ)

/-- `toExtZero φ` is the Ext⁰ class of the identity-cube algebra map of `φ`. -/
theorem toExtZero_spec {L : FlatLift t f} (φ : ReduceIdAuto L) :
    toExtZero φ = extZeroOfAlgebraMap (autoAlgebraMap φ)
        (autoAlgebraMap_commutes φ) (autoAlgebraMap_isAlgebra φ) ∧
      ofExtZero L (toExtZero φ) = φ := sorry

/-- The identity automorphism is the image of the zero Ext⁰ class. -/
theorem ofExtZero_zero (L : FlatLift t f) :
    ofExtZero L 0 = ReduceIdAuto.id L := sorry

end FlatLift
end AlgebraicGeometry.AlgebraicSpace.Thickening
