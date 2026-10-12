/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Monoidal
public import ReasLib.Algebra.Homology.ComplexShapeSigns.Nat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Pushforward.Comparison
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.ExternalTensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.AlgebraicTopology.SimplexCategory.FrontBack

/-!
# Čech comparison for external tensor products

Two open covers on schemes over a common base determine a product cover on the fibre product.
The Alexander--Whitney front and back coordinates give a canonical comparison from the tensor
total of the two pushed-forward Čech complexes to the pushed-forward Čech complex of the product
cover with external-tensor coefficients.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.OpenCoverCech.Kunneth

/-- The degree component of the Čech comparison for external tensor products. -/
@[stacks 0BEE]
noncomputable def component
    {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    (𝒰 : X.OpenCover) (𝒱 : Y.OpenCover) (F : X.Modules) (G : Y.Modules)
    (n : ℕ) :
    (HomologicalComplex.tensorObj
      (OpenCoverCech.pushforward a
        (fun i : 𝒰.I₀ ↦ (𝒰.f i).opensRange) F)
      (OpenCoverCech.pushforward b
        (fun j : 𝒱.I₀ ↦ (𝒱.f j).opensRange) G)).X n ⟶
      (OpenCoverCech.pushforward (pullback.fst a b ≫ a)
        (fun ij : 𝒰.I₀ × 𝒱.I₀ ↦
          ((Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒱 a b).f ij).opensRange)
        (Scheme.Modules.externalTensorProduct a b F G)).X n :=
  -- The remaining local coordinate maps are proof-local construction data tied to the
  -- Alexander--Whitney component and are not competing public choices.
  by
  let externalMap (A : X.Modules) (B : Y.Modules) :
      tensorObj ((Scheme.Modules.pushforward a).obj A)
          ((Scheme.Modules.pushforward b).obj B) ⟶
        (Scheme.Modules.pushforward (pullback.fst a b ≫ a)).obj
          (Scheme.Modules.externalTensorProduct a b A B) :=
    (Scheme.Modules.pullbackPushforwardAdjunction (pullback.fst a b ≫ a)).homEquiv _ _
      (Scheme.Modules.pullbackTensorComparison (pullback.fst a b ≫ a)
          ((Scheme.Modules.pushforward a).obj A)
          ((Scheme.Modules.pushforward b).obj B) ≫
        (((Scheme.Modules.pullbackComp (pullback.fst a b) a).inv.app
            ((Scheme.Modules.pushforward a).obj A) ≫
          (Scheme.Modules.pullback (pullback.fst a b)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction a).counit.app A)) ⊗ₘ
        ((Scheme.Modules.pullbackCongr (pullback.condition :
            pullback.fst a b ≫ a = pullback.snd a b ≫ b)).hom.app
              ((Scheme.Modules.pushforward b).obj B) ≫
          (Scheme.Modules.pullbackComp (pullback.snd a b) b).inv.app
            ((Scheme.Modules.pushforward b).obj B) ≫
          (Scheme.Modules.pullback (pullback.snd a b)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction b).counit.app B))))
  let pullbackOpenMap {P Z : RingedSpace.{u}} (r : P ⟶ Z)
      (U : TopologicalSpace.Opens Z.carrier)
      (W : TopologicalSpace.Opens P.carrier)
      (hW : W ≤ RingedSpace.preimageOpen r U) (A : RingedSpace.Modules Z) :
      (RingedSpace.Hom.pullback r).obj
          ((RingedSpace.modulePushforwardFromOpen U).obj
            ((RingedSpace.moduleRestrictionToOpen Z U).obj A)) ⟶
        (RingedSpace.modulePushforwardFromOpen W).obj
          ((RingedSpace.moduleRestrictionToOpen P W).obj
            ((RingedSpace.Hom.pullback r).obj A)) := by
    let iW := P.ofRestrict W.isOpenEmbedding
    let iU := Z.ofRestrict U.isOpenEmbedding
    let t := RingedSpace.restrictedMorphismBetweenOpens P hW ≫
      RingedSpace.restrictedMorphismToOpen r U
    have ht : t ≫ iU = iW ≫ r := by
      dsimp [t, iU, iW]
      rw [Category.assoc, RingedSpace.restrictedMorphismToOpen_fac,
        ← Category.assoc, RingedSpace.restrictedMorphismBetweenOpens_fac]
    let e : RingedSpace.Hom.pullback (iW ≫ r) ≅
        RingedSpace.Hom.pullback (t ≫ iU) :=
      eqToIso (congrArg RingedSpace.Hom.pullback ht.symm)
    exact
      (RingedSpace.OpenSubspace.Pushforward.adjunction P W).homEquiv _ _
        ((RingedSpace.Hom.pullbackCompIso iW r).inv.app _ ≫
          e.hom.app _ ≫
          (RingedSpace.Hom.pullbackCompIso t iU).hom.app _ ≫
          (RingedSpace.Hom.pullback t).map
            ((RingedSpace.Hom.pullbackPushforwardAdjunction iU).counit.app
              ((RingedSpace.moduleRestrictionToOpen Z U).obj A)) ≫
          (RingedSpace.Hom.pullbackCompIso t iU).inv.app _ ≫
          e.inv.app _ ≫
          (RingedSpace.Hom.pullbackCompIso iW r).hom.app A)
  let openTensorMap {P : RingedSpace.{u}} (W : TopologicalSpace.Opens P.carrier)
      (A B : RingedSpace.Modules P) :
      tensorObj
          ((RingedSpace.modulePushforwardFromOpen W).obj
            ((RingedSpace.moduleRestrictionToOpen P W).obj A))
          ((RingedSpace.modulePushforwardFromOpen W).obj
            ((RingedSpace.moduleRestrictionToOpen P W).obj B)) ⟶
        (RingedSpace.modulePushforwardFromOpen W).obj
          ((RingedSpace.moduleRestrictionToOpen P W).obj (tensorObj A B)) :=
    let iW := P.ofRestrict W.isOpenEmbedding
    (RingedSpace.OpenSubspace.Pushforward.adjunction P W).homEquiv _ _
      (RingedSpace.Hom.pullbackTensorComparison iW
          ((RingedSpace.modulePushforwardFromOpen W).obj
            ((RingedSpace.moduleRestrictionToOpen P W).obj A))
          ((RingedSpace.modulePushforwardFromOpen W).obj
            ((RingedSpace.moduleRestrictionToOpen P W).obj B)) ≫
        (((RingedSpace.OpenSubspace.Pushforward.adjunction P W).counit.app
            ((RingedSpace.moduleRestrictionToOpen P W).obj A)) ⊗ₘ
          ((RingedSpace.OpenSubspace.Pushforward.adjunction P W).counit.app
            ((RingedSpace.moduleRestrictionToOpen P W).obj B))) ≫
        (RingedSpace.Hom.pullbackTensorIso iW A B).inv)
  let coverFst (ij : 𝒰.I₀ × 𝒱.I₀) :
      (Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒱 a b).X ij ⟶ 𝒰.X ij.1 :=
    eqToHom (Scheme.Pullback.openCoverOfLeftRight_X 𝒰 𝒱 a b ij) ≫
      pullback.fst (𝒰.f ij.1 ≫ a) (𝒱.f ij.2 ≫ b)
  have coverFst_fac (ij : 𝒰.I₀ × 𝒱.I₀) :
      (Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒱 a b).f ij ≫ pullback.fst a b =
        coverFst ij ≫ 𝒰.f ij.1 := by
    rw [Scheme.Pullback.openCoverOfLeftRight_f]
    change pullback.map (𝒰.f ij.1 ≫ a) (𝒱.f ij.2 ≫ b) a b
        (𝒰.f ij.1) (𝒱.f ij.2) (𝟙 S) _ _ ≫ pullback.fst a b =
      pullback.fst (𝒰.f ij.1 ≫ a) (𝒱.f ij.2 ≫ b) ≫ 𝒰.f ij.1
    exact pullback.lift_fst _ _ _
  let coverSnd (ij : 𝒰.I₀ × 𝒱.I₀) :
      (Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒱 a b).X ij ⟶ 𝒱.X ij.2 :=
    eqToHom (Scheme.Pullback.openCoverOfLeftRight_X 𝒰 𝒱 a b ij) ≫
      pullback.snd (𝒰.f ij.1 ≫ a) (𝒱.f ij.2 ≫ b)
  have coverSnd_fac (ij : 𝒰.I₀ × 𝒱.I₀) :
      (Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒱 a b).f ij ≫ pullback.snd a b =
        coverSnd ij ≫ 𝒱.f ij.2 := by
    rw [Scheme.Pullback.openCoverOfLeftRight_f]
    change pullback.map (𝒰.f ij.1 ≫ a) (𝒱.f ij.2 ≫ b) a b
        (𝒰.f ij.1) (𝒱.f ij.2) (𝟙 S) _ _ ≫ pullback.snd a b =
      pullback.snd (𝒰.f ij.1 ≫ a) (𝒱.f ij.2 ≫ b) ≫ 𝒱.f ij.2
    exact pullback.lift_snd _ _ _
  have rangeFst (ij : 𝒰.I₀ × 𝒱.I₀) :
      ((Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒱 a b).f ij).opensRange ≤
        pullback.fst a b ⁻¹ᵁ (𝒰.f ij.1).opensRange := by
    change Set.range ((Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒱 a b).f ij).base ⊆ _
    rintro _ ⟨z, rfl⟩
    refine ⟨(coverFst ij).base z, ?_⟩
    simpa [Scheme.Hom.comp_base, ConcreteCategory.comp_apply] using
      congrArg (fun f : Scheme.Hom _ _ ↦ f.base z) (coverFst_fac ij).symm
  have rangeSnd (ij : 𝒰.I₀ × 𝒱.I₀) :
      ((Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒱 a b).f ij).opensRange ≤
        pullback.snd a b ⁻¹ᵁ (𝒱.f ij.2).opensRange := by
    change Set.range ((Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒱 a b).f ij).base ⊆ _
    rintro _ ⟨z, rfl⟩
    refine ⟨(coverSnd ij).base z, ?_⟩
    simpa [Scheme.Hom.comp_base, ConcreteCategory.comp_apply] using
      congrArg (fun f : Scheme.Hom _ _ ↦ f.base z) (coverSnd_fac ij).symm
  let 𝒰' : 𝒰.I₀ → X.Opens := fun i ↦ (𝒰.f i).opensRange
  let 𝒱' : 𝒱.I₀ → Y.Opens := fun j ↦ (𝒱.f j).opensRange
  let 𝒲 : 𝒰.I₀ × 𝒱.I₀ → (pullback a b).Opens :=
    fun ij ↦ ((Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒱 a b).f ij).opensRange
  let summand (p q : ℕ) (hpq : p + q = n) :
      tensorObj
          ((OpenCoverCech.pushforward a 𝒰' F).X p)
          ((OpenCoverCech.pushforward b 𝒱' G).X q) ⟶
        (OpenCoverCech.pushforward (pullback.fst a b ≫ a) 𝒲
          (Scheme.Modules.externalTensorProduct a b F G)).X n := by
    refine externalMap (openCoverModuleCechTerm 𝒰' F p)
        (openCoverModuleCechTerm 𝒱' G q) ≫
      (Scheme.Modules.pushforward (pullback.fst a b ≫ a)).map (Pi.lift fun ω ↦ ?_)
    let front : Fin (p + 1) → 𝒰.I₀ :=
      fun i ↦ (ω ((SimplexCategory.frontOfAddEq p q n hpq).toOrderHom i)).1
    let back : Fin (q + 1) → 𝒱.I₀ :=
      fun j ↦ (ω ((SimplexCategory.backOfAddEq p q n hpq).toOrderHom j)).2
    let U := TopCat.Presheaf.Cech.intersection 𝒰' front
    let V := TopCat.Presheaf.Cech.intersection 𝒱' back
    let W := TopCat.Presheaf.Cech.intersection 𝒲 ω
    have hU : W ≤ RingedSpace.preimageOpen (pullback.fst a b).toLRSHom.toShHom U := by
      change (⨅ i, 𝒲 (ω i)) ≤
        RingedSpace.preimageOpen (pullback.fst a b).toLRSHom.toShHom
          (⨅ i, 𝒰' (front i))
      rw [show RingedSpace.preimageOpen (pullback.fst a b).toLRSHom.toShHom
          (⨅ i, 𝒰' (front i)) =
        ⨅ i, RingedSpace.preimageOpen (pullback.fst a b).toLRSHom.toShHom
          (𝒰' (front i)) by
        apply Opens.ext
        simp only [Opens.map_coe, Opens.coe_iInf, Set.preimage_iInter]]
      refine le_iInf fun i ↦ le_trans (iInf_le (fun j ↦ 𝒲 (ω j))
        ((SimplexCategory.frontOfAddEq p q n hpq).toOrderHom i)) ?_
      exact rangeFst
        (ω ((SimplexCategory.frontOfAddEq p q n hpq).toOrderHom i))
    have hV : W ≤ RingedSpace.preimageOpen (pullback.snd a b).toLRSHom.toShHom V := by
      change (⨅ j, 𝒲 (ω j)) ≤
        RingedSpace.preimageOpen (pullback.snd a b).toLRSHom.toShHom
          (⨅ j, 𝒱' (back j))
      rw [show RingedSpace.preimageOpen (pullback.snd a b).toLRSHom.toShHom
          (⨅ j, 𝒱' (back j)) =
        ⨅ j, RingedSpace.preimageOpen (pullback.snd a b).toLRSHom.toShHom
          (𝒱' (back j)) by
        apply Opens.ext
        simp only [Opens.map_coe, Opens.coe_iInf, Set.preimage_iInter]]
      refine le_iInf fun j ↦ le_trans (iInf_le (fun i ↦ 𝒲 (ω i))
        ((SimplexCategory.backOfAddEq p q n hpq).toOrderHom j)) ?_
      exact rangeSnd
        (ω ((SimplexCategory.backOfAddEq p q n hpq).toOrderHom j))
    exact
      (((Scheme.Modules.pullback (pullback.fst a b)).map
          (Pi.π (openCoverModuleCechSummand 𝒰' F p) front) ≫
        pullbackOpenMap (pullback.fst a b).toLRSHom.toShHom U W hU F) ⊗ₘ
      ((Scheme.Modules.pullback (pullback.snd a b)).map
          (Pi.π (openCoverModuleCechSummand 𝒱' G q) back) ≫
        pullbackOpenMap (pullback.snd a b).toLRSHom.toShHom V W hV G)) ≫
      openTensorMap W
        ((Scheme.Modules.pullback (pullback.fst a b)).obj F)
        ((Scheme.Modules.pullback (pullback.snd a b)).obj G)
  exact HomologicalComplex.mapBifunctorDesc summand

/-- The degree components of the Čech comparison commute with the differentials. -/
@[stacks 0BEE]
theorem component_comm
    {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    (𝒰 : X.OpenCover) (𝒱 : Y.OpenCover) (F : X.Modules) (G : Y.Modules) :
    ∀ i j, (ComplexShape.up ℕ).Rel i j →
      component a b 𝒰 𝒱 F G i ≫
          (OpenCoverCech.pushforward (pullback.fst a b ≫ a)
            (fun ij : 𝒰.I₀ × 𝒱.I₀ ↦
              ((Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒱 a b).f ij).opensRange)
            (Scheme.Modules.externalTensorProduct a b F G)).d i j =
        (HomologicalComplex.tensorObj
          (OpenCoverCech.pushforward a
            (fun k : 𝒰.I₀ ↦ (𝒰.f k).opensRange) F)
          (OpenCoverCech.pushforward b
            (fun k : 𝒱.I₀ ↦ (𝒱.f k).opensRange) G)).d i j ≫
          component a b 𝒰 𝒱 F G j := sorry

/-- The canonical Čech comparison from the tensor total to the product-cover complex. -/
@[stacks 0BEE]
noncomputable def comparison
    {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    (𝒰 : X.OpenCover) (𝒱 : Y.OpenCover) (F : X.Modules) (G : Y.Modules) :
    HomologicalComplex.tensorObj
        (OpenCoverCech.pushforward a
          (fun i : 𝒰.I₀ ↦ (𝒰.f i).opensRange) F)
        (OpenCoverCech.pushforward b
          (fun j : 𝒱.I₀ ↦ (𝒱.f j).opensRange) G) ⟶
      OpenCoverCech.pushforward (pullback.fst a b ≫ a)
        (fun ij : 𝒰.I₀ × 𝒱.I₀ ↦
          ((Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒱 a b).f ij).opensRange)
        (Scheme.Modules.externalTensorProduct a b F G) :=
  HomologicalComplex.Hom.mk
    (component a b 𝒰 𝒱 F G)
    (component_comm a b 𝒰 𝒱 F G)

/-- Evaluating the Čech comparison gives its front-back coordinate component. -/
@[stacks 0BEE, simp]
theorem comparison_f
    {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    (𝒰 : X.OpenCover) (𝒱 : Y.OpenCover) (F : X.Modules) (G : Y.Modules)
    (n : ℕ) :
    (comparison a b 𝒰 𝒱 F G).f n =
      component a b 𝒰 𝒱 F G n := sorry

/-- The degree component of the Čech comparison after taking global sections over `Spec A`. -/
noncomputable def componentOverSpec
    {A : Type u} [CommRing A] {X Y : Scheme.{u}}
    (a : X ⟶ Spec (CommRingCat.of A)) (b : Y ⟶ Spec (CommRingCat.of A))
    (𝒰 : X.OpenCover) (𝒱 : Y.OpenCover) (F : X.Modules) (G : Y.Modules)
    (n : ℕ) :
    (HomologicalComplex.tensorObj
      (OpenCoverCech.globalSectionsOverSpec a 𝒰 F)
      (OpenCoverCech.globalSectionsOverSpec b 𝒱 G)).X n ⟶
      (OpenCoverCech.globalSectionsOverSpec (pullback.fst a b ≫ a)
        (Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒱 a b)
        (Scheme.Modules.externalTensorProduct a b F G)).X n :=
  let H := RingedSpace.moduleGlobalSectionsRestrictionFunctor
    (Spec (CommRingCat.of A)).toRingedSpace
      (Scheme.Hom.globalSectionsMap (𝟙 (Spec (CommRingCat.of A))))
  let hH : H.LaxMonoidal :=
    RingedSpace.moduleGlobalSectionsRestrictionFunctorLaxMonoidal
      (Spec (CommRingCat.of A)).toRingedSpace
        (Scheme.Hom.globalSectionsMap (𝟙 (Spec (CommRingCat.of A))))
  let K := OpenCoverCech.pushforward a
    (fun i : 𝒰.I₀ ↦ (𝒰.f i).opensRange) F
  let L := OpenCoverCech.pushforward b
    (fun j : 𝒱.I₀ ↦ (𝒱.f j).opensRange) G
  HomologicalComplex.mapBifunctorDesc fun p q hpq ↦
    @Functor.LaxMonoidal.μ _ _ _ _ _ _ H hH (K.X p) (L.X q) ≫
      H.map (HomologicalComplex.ιTensorObj K L p q n hpq ≫
        component a b 𝒰 𝒱 F G n)

/-- The global-sections Čech comparison components commute with the differentials. -/
theorem componentOverSpec_comm
    {A : Type u} [CommRing A] {X Y : Scheme.{u}}
    (a : X ⟶ Spec (CommRingCat.of A)) (b : Y ⟶ Spec (CommRingCat.of A))
    (𝒰 : X.OpenCover) (𝒱 : Y.OpenCover) (F : X.Modules) (G : Y.Modules) :
    ∀ i j, (ComplexShape.up ℕ).Rel i j →
      componentOverSpec a b 𝒰 𝒱 F G i ≫
          (OpenCoverCech.globalSectionsOverSpec (pullback.fst a b ≫ a)
            (Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒱 a b)
            (Scheme.Modules.externalTensorProduct a b F G)).d i j =
        (HomologicalComplex.tensorObj
          (OpenCoverCech.globalSectionsOverSpec a 𝒰 F)
          (OpenCoverCech.globalSectionsOverSpec b 𝒱 G)).d i j ≫
          componentOverSpec a b 𝒰 𝒱 F G j := sorry

/-- The Čech comparison over `Spec A` from the tensor total of global-sections complexes to the
global-sections complex of the product cover. -/
@[stacks 0FLU]
noncomputable def comparisonOverSpec
    {A : Type u} [CommRing A] {X Y : Scheme.{u}}
    (a : X ⟶ Spec (CommRingCat.of A)) (b : Y ⟶ Spec (CommRingCat.of A))
    (𝒰 : X.OpenCover) (𝒱 : Y.OpenCover) (F : X.Modules) (G : Y.Modules) :
    HomologicalComplex.tensorObj
        (OpenCoverCech.globalSectionsOverSpec a 𝒰 F)
        (OpenCoverCech.globalSectionsOverSpec b 𝒱 G) ⟶
      OpenCoverCech.globalSectionsOverSpec (pullback.fst a b ≫ a)
        (Scheme.Pullback.openCoverOfLeftRight 𝒰 𝒱 a b)
        (Scheme.Modules.externalTensorProduct a b F G) :=
  HomologicalComplex.Hom.mk
    (componentOverSpec a b 𝒰 𝒱 F G)
    (componentOverSpec_comm a b 𝒰 𝒱 F G)

/-- Evaluating the global-sections Čech comparison gives its degree component. -/
@[simp]
theorem comparisonOverSpec_f
    {A : Type u} [CommRing A] {X Y : Scheme.{u}}
    (a : X ⟶ Spec (CommRingCat.of A)) (b : Y ⟶ Spec (CommRingCat.of A))
    (𝒰 : X.OpenCover) (𝒱 : Y.OpenCover) (F : X.Modules) (G : Y.Modules)
    (n : ℕ) :
    (comparisonOverSpec a b 𝒰 𝒱 F G).f n =
      componentOverSpec a b 𝒰 𝒱 F G n := sorry

end AlgebraicGeometry.Scheme.OpenCoverCech.Kunneth

end
