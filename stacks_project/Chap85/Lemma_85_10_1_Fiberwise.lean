/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import stacks_project.Chap85.Lemma_85_6_1_Fiber

/-!
# Alternating-face complex of `g_{n!} O_n` on a fiberwise simplicial site

In Situation 85.3.3 case B, the simplicial sheaf of `O`-modules `n ↦ g_{n!} O_n`
on the total Grothendieck construction, its augmentation to the rank-one sheaf
`O`, and the associated alternating-face chain complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open HomologicalComplex RingedSite
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable (O : Sheaf (topology F J) RingCat.{w})
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology F J).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J O φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology F J).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The rank-one sheaf of modules `O_n` on the degree-`n` fiber. -/
abbrev fiberComponentUnit (n : SimplexCategory) :
    SheafOfModules.{w} (fiberComponentRingSheaf F J O n) :=
  SheafOfModules.unit (fiberComponentRingSheaf F J O n)

/-- Unfolding `fiberComponentUnit` recovers `SheafOfModules.unit` on `O_n`. -/
theorem fiberComponentUnit_eq (n : SimplexCategory) :
    fiberComponentUnit F J O n = SheafOfModules.unit (fiberComponentRingSheaf F J O n) :=
  sorry

/-- Underlying type-valued map of the rank-one pushforward comparison along `f_φ`. -/
def fiberFacePushforward_unit_underlying {n m : SimplexCategory} (φ : n ⟶ m) :
    (Sheaf.InternalModule.ToInternal.underlying (fiberComponentRingSheaf F J O n)).obj
        (fiberComponentUnit F J O n) ⟶
      (Sheaf.InternalModule.ToInternal.underlying (fiberComponentRingSheaf F J O n)).obj
        ((fiberRingedToposMap F J O φ).modulePushforward.obj
          (fiberComponentUnit F J O m)) :=
  (fiberRingedToposMap F J O φ).underlyingDirectImageMap ≫
    (ToposHom.ModulePushforward.forgetIso
      (fiberRingedToposMap F J O φ)).inv.app (fiberComponentUnit F J O m)

/-- Additivity of `fiberFacePushforward_unit_underlying`. -/
theorem fiberFacePushforward_unit_add {n m : SimplexCategory} (φ : n ⟶ m) :
    ∀ U (x y : (fiberComponentUnit F J O n).val.obj U),
      Sheaf.InternalModule.underlyingApp (fiberComponentRingSheaf F J O n)
        (fiberFacePushforward_unit_underlying F J O φ) U (x + y) =
      Sheaf.InternalModule.underlyingApp (fiberComponentRingSheaf F J O n)
        (fiberFacePushforward_unit_underlying F J O φ) U x +
      Sheaf.InternalModule.underlyingApp (fiberComponentRingSheaf F J O n)
        (fiberFacePushforward_unit_underlying F J O φ) U y :=
  sorry

/-- Linearity of `fiberFacePushforward_unit_underlying`. -/
theorem fiberFacePushforward_unit_smul {n m : SimplexCategory} (φ : n ⟶ m) :
    ∀ U (r : (fiberComponentRingSheaf F J O n).obj.obj U)
      (x : (fiberComponentUnit F J O n).val.obj U),
      Sheaf.InternalModule.underlyingApp (fiberComponentRingSheaf F J O n)
        (fiberFacePushforward_unit_underlying F J O φ) U (r • x) =
      r • Sheaf.InternalModule.underlyingApp (fiberComponentRingSheaf F J O n)
        (fiberFacePushforward_unit_underlying F J O φ) U x :=
  sorry

/-- The comparison `O_n ⟶ f_φ_* O_m` of rank-one modules along a fiberwise simplex
operator, lifted from the forgotten direct-image structure map. -/
def fiberFacePushforward_unit {n m : SimplexCategory} (φ : n ⟶ m) :
    fiberComponentUnit F J O n ⟶
      (fiberRingedToposMap F J O φ).modulePushforward.obj
        (fiberComponentUnit F J O m) :=
  Sheaf.InternalModule.homOfUnderlying (fiberComponentRingSheaf F J O n)
    (fiberFacePushforward_unit_underlying F J O φ)
    (fiberFacePushforward_unit_add F J O φ)
    (fiberFacePushforward_unit_smul F J O φ)

/-- The comparison `f_φ^* O_n ⟶ O_m` of rank-one modules, the adjunct of
`fiberFacePushforward_unit`. -/
def fiberFacePullback_unit_counit {n m : SimplexCategory} (φ : n ⟶ m) :
    (fiberRingedToposMap F J O φ).modulePullback.obj (fiberComponentUnit F J O n) ⟶
      fiberComponentUnit F J O m :=
  ((fiberRingedToposMap F J O φ).moduleAdjunction.homEquiv
      (fiberComponentUnit F J O n) (fiberComponentUnit F J O m)).symm
    (fiberFacePushforward_unit F J O φ)

/-- The comparison `f_φ^* O_n ⟶ O_m` is an isomorphism. -/
instance fiberFacePullback_unit_counit_isIso {n m : SimplexCategory} (φ : n ⟶ m) :
    IsIso (fiberFacePullback_unit_counit F J O φ) :=
  sorry

/-- The comparison `O_m ⟶ f_φ^* O_n` of rank-one modules along a fiberwise simplex
operator. -/
def fiberFacePullback_unit {n m : SimplexCategory} (φ : n ⟶ m) :
    fiberComponentUnit F J O m ⟶
      (fiberRingedToposMap F J O φ).modulePullback.obj (fiberComponentUnit F J O n) :=
  CategoryTheory.inv (fiberFacePullback_unit_counit F J O φ)

/-- The comparison `O_m ⟶ f_φ^* O_n` is an isomorphism in case B. -/
instance fiberFacePullback_unit_isIso {n m : SimplexCategory} (φ : n ⟶ m) :
    IsIso (fiberFacePullback_unit F J O φ) :=
  sorry

/-- The identity comparison `O_n ⟶ (ι F (op n))_* O` of ring sheaves, pinning
the site functor to `ι F (op n)` rather than the identity on the fiber. -/
def fiberInclusion_identityRingMap (n : SimplexCategory) :
    fiberComponentRingSheaf F J O n ⟶
      ((ι F (op n)).sheafPushforwardContinuous RingCat.{w}
        (J (op n)).toGrothendieck (topology F J)).obj O :=
  𝟙 (fiberComponentRingSheaf F J O n)

/-- `fiberInclusion_identityRingMap` is the identity on `O_n`. -/
theorem fiberInclusion_identityRingMap_eq (n : SimplexCategory) :
    fiberInclusion_identityRingMap F J O n = 𝟙 (fiberComponentRingSheaf F J O n) :=
  sorry

/-- The comparison `O_n ⟶ g_n^* O` of rank-one modules along `ι F (op n)`. -/
def fiberInclusion_unit_hom (n : SimplexCategory) :
    fiberComponentUnit F J O n ⟶
      (Cocontinuous.moduleInverseImage (ι F (op n)) O).obj
        (SheafOfModules.unit O) :=
  SheafOfModules.unitToPushforwardObjUnit (fiberInclusion_identityRingMap F J O n)

/-- `fiberInclusion_unit_hom` is the unit-module map of `fiberInclusion_identityRingMap`. -/
theorem fiberInclusion_unit_hom_eq (n : SimplexCategory) :
    fiberInclusion_unit_hom F J O n =
      SheafOfModules.unitToPushforwardObjUnit
        (fiberInclusion_identityRingMap F J O n) :=
  sorry

/-- The adjunct of `fiberFacePullback_unit ≫ fiberModuleLowerShriek_component`
along `g_{m!} ⊣ g_m^*`. -/
def fiberLowerShriekUnit_map {n m : SimplexCategory} (φ : n ⟶ m) :
    (fiberModuleLowerShriek F J O m).obj (fiberComponentUnit F J O m) ⟶
      (fiberModuleLowerShriek F J O n).obj (fiberComponentUnit F J O n) :=
  ((fiberModuleLowerShriek.adjunction F J O m).homEquiv
      (fiberComponentUnit F J O m)
      ((fiberModuleLowerShriek F J O n).obj (fiberComponentUnit F J O n))).symm
    (fiberFacePullback_unit F J O φ ≫
      fiberModuleLowerShriek_component F J O φ (fiberComponentUnit F J O n) ≫
      (fiberModuleInverseImageIsoModulePullback F J O m).inv.app
        ((fiberModuleLowerShriek F J O n).obj (fiberComponentUnit F J O n)))

/-- Identity simplex operators induce identity structure maps in case B. -/
theorem fiberLowerShriekUnit_map_id (n : SimplexCategory) :
    fiberLowerShriekUnit_map F J O (𝟙 n) =
      𝟙 ((fiberModuleLowerShriek F J O n).obj (fiberComponentUnit F J O n)) :=
  sorry

/-- Structure maps of `n ↦ g_{n!} O_n` are functorial in fiberwise simplex operators. -/
theorem fiberLowerShriekUnit_map_comp {l n m : SimplexCategory}
    (ψ : l ⟶ n) (φ : n ⟶ m) :
    fiberLowerShriekUnit_map F J O (ψ ≫ φ) =
      fiberLowerShriekUnit_map F J O φ ≫ fiberLowerShriekUnit_map F J O ψ :=
  sorry

/-- Opposite identity operators act as identity maps in case B. -/
theorem fiberLowerShriekUnit_map_id_op (n : SimplexCategoryᵒᵖ) :
    fiberLowerShriekUnit_map F J O (𝟙 n.unop) =
      𝟙 ((fiberModuleLowerShriek F J O n.unop).obj (fiberComponentUnit F J O n.unop)) :=
  sorry

/-- Opposite composition of simplex operators acts as composition of structure maps
in case B. -/
theorem fiberLowerShriekUnit_map_comp_op {n m p : SimplexCategoryᵒᵖ}
    (f : n ⟶ m) (g : m ⟶ p) :
    fiberLowerShriekUnit_map F J O (f ≫ g).unop =
      fiberLowerShriekUnit_map F J O f.unop ≫ fiberLowerShriekUnit_map F J O g.unop :=
  sorry

/-- The simplicial sheaf of `O`-modules `n ↦ g_{n!} O_n` on the total fiberwise site. -/
def fiberLowerShriekUnit : SimplicialObject (SheafOfModules.{w} O) where
  obj n := (fiberModuleLowerShriek F J O n.unop).obj (fiberComponentUnit F J O n.unop)
  map f := fiberLowerShriekUnit_map F J O f.unop
  map_id := fiberLowerShriekUnit_map_id_op F J O
  map_comp := fiberLowerShriekUnit_map_comp_op F J O

/-- The value of `fiberLowerShriekUnit` at `n` is `g_{n!} O_n`. -/
theorem fiberLowerShriekUnit_obj (n : SimplexCategory) :
    (fiberLowerShriekUnit F J O).obj (op n) =
      (fiberModuleLowerShriek F J O n).obj (fiberComponentUnit F J O n) :=
  sorry

/-- The source face map `d_i : g_{(n+1)!} O_{n+1} ⟶ g_{n!} O_n` in case B. -/
def fiberModuleFace (n : ℕ) (i : Fin (n + 2)) :
    (fiberLowerShriekUnit F J O).obj (op ⦋n + 1⦌) ⟶
      (fiberLowerShriekUnit F J O).obj (op ⦋n⦌) :=
  (fiberLowerShriekUnit F J O).δ i

/-- The face map `fiberModuleFace i` is the simplicial operator `δ i`. -/
theorem fiberModuleFace_eq (n : ℕ) (i : Fin (n + 2)) :
    fiberModuleFace F J O n i = (fiberLowerShriekUnit F J O).δ i :=
  sorry

/-- The component of the case B augmentation `g_{n!} O_n ⟶ O` at a simplex `n`. -/
def fiberModuleAugmented_hom_app (n : SimplexCategoryᵒᵖ) :
    (fiberLowerShriekUnit F J O).obj n ⟶ SheafOfModules.unit O :=
  ((fiberModuleLowerShriek.adjunction F J O n.unop).homEquiv
      (fiberComponentUnit F J O n.unop) (SheafOfModules.unit O)).symm
    (fiberInclusion_unit_hom F J O n.unop)

/-- Naturality of the degreewise case B augmentation `g_{n!} O_n ⟶ O`. -/
theorem fiberModuleAugmented_hom_naturality :
    ∀ ⦃n m : SimplexCategoryᵒᵖ⦄ (f : n ⟶ m),
      (fiberLowerShriekUnit F J O).map f ≫ fiberModuleAugmented_hom_app F J O m =
        fiberModuleAugmented_hom_app F J O n ≫
          ((SimplicialObject.const _).obj (SheafOfModules.unit O)).map f :=
  sorry

/-- The natural transformation `n ↦ g_{n!} O_n ⟶ const O` in case B. -/
def fiberModuleAugmented_hom :
    fiberLowerShriekUnit F J O ⟶
      (SimplicialObject.const _).obj (SheafOfModules.unit O) where
  app := fiberModuleAugmented_hom_app F J O
  naturality := fiberModuleAugmented_hom_naturality F J O

/-- The augmented simplicial object of `g_{n!} O_n` over the rank-one sheaf `O` in case B. -/
def fiberModuleAugmented : SimplicialObject.Augmented (SheafOfModules.{w} O) where
  left := fiberLowerShriekUnit F J O
  right := SheafOfModules.unit O
  hom := fiberModuleAugmented_hom F J O

/-- The alternating-face chain complex `… → g_{2!} O_2 → g_{1!} O_1 → g_{0!} O_0` in case B. -/
abbrev fiberModuleComplex : ChainComplex (SheafOfModules.{w} O) ℕ :=
  (alternatingFaceMapComplex _).obj
    (SimplicialObject.Augmented.drop.obj (fiberModuleAugmented F J O))

/-- Degree `n` of `fiberModuleComplex F J O` is the sheaf of modules `g_{n!} O_n`. -/
theorem fiberModuleComplex_X (n : ℕ) :
    (fiberModuleComplex F J O).X n =
      (fiberModuleLowerShriek F J O ⦋n⦌).obj (fiberComponentUnit F J O ⦋n⦌) :=
  sorry

/-- Differentials of `fiberModuleComplex F J O` are the alternating sums of face maps. -/
theorem fiberModuleComplex_d_eq (n : ℕ) :
    (fiberModuleComplex F J O).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • fiberModuleFace F J O n i :=
  sorry

/-- The canonical chain-map augmentation from `fiberModuleComplex F J O` to the rank-one
sheaf `O` concentrated in degree zero. -/
def fiberModuleAugmentation :
    fiberModuleComplex F J O ⟶
      (ChainComplex.single₀ _).obj (SheafOfModules.unit O) :=
  AlternatingFaceMapComplex.ε.app (fiberModuleAugmented F J O)

/-- The degree-zero component of `fiberModuleAugmentation F J O` is the simplicial
augmentation at `⦋0⦌`. -/
theorem fiberModuleAugmentation_f_zero :
    (fiberModuleAugmentation F J O).f 0 =
      (fiberModuleAugmented F J O).hom.app (op ⦋0⦌) :=
  sorry

end CategoryTheory.Grothendieck
