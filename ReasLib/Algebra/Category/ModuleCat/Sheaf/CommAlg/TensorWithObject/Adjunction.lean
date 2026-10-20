/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.DifferentialGraded.Representable.Functor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CommAlg.TensorWithObject

/-!
# Tensor-representable adjunction over an algebra sheaf

This file constructs the coefficient-linear currying equivalence for sectionwise relative
tensoring over `endDGA K`.  The presheaf-level construction is integral, while the final
homogeneous Hom equivalence records the canonical linearity over the coefficient ring `R`.
It then descends the equivalence to closed maps and enriched homotopy categories.
-/

@[expose] public section

noncomputable section

universe r u v w z

open CategoryTheory
open CochainComplex.HomComplex
open DifferentialGradedCategory
open HomologicalComplex
open scoped DifferentialGradedCategory SheafOfModules.CommAlg
open SheafOfModules.RingedSite.ModuleSheafification

namespace SheafOfModules.CommAlg.TensorWithObject

variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ (CommAlgCat.{w} R) CommRingCat.{w})]
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{max u z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u z}]
variable {O : Sheaf J (CommAlgCat.{w} R)}

/-- Pure tensor formation after fixing a homogeneous right-module element, as a morphism of
module presheaves in the remaining section variable. -/
@[stacks 09LY "pure tensors in the arbitrary-ring sectionwise construction"]
def tmulPresheaf (K : Complex.{r, u, v, w, max u z} O) (M : Modules K)
    (p q : ℤ) (m : M.X p) : (K.X q).val ⟶ term K M (p + q) where
  app U := ModuleCat.ofHom
    { toFun := fun x ↦
        DifferentialGradedModule.TensorProduct.tmul M (sectionModule K U) m x
      map_add' := sorry
      map_smul' := sorry }
  naturality := sorry

/-- Reassociation of the target degree in sectionwise homogeneous currying. -/
@[stacks 09LY "degree reassociation for arbitrary-ring currying"]
theorem curryDegree (p q k n : ℤ) (h : q + (p + k) = n) :
    (p + q) + k = n := sorry

/-- Curry a presheaf cochain after fixing a homogeneous element of the right DG module. -/
@[stacks 09LY "arbitrary-ring sectionwise curried cochain"]
def curryCochain (K : Complex.{r, u, v, w, max u z} O) (M : Modules K)
    (X : Complex.{r, u, v, w, max u z} O) {k : ℤ}
    (f : Cochain (presheafComplex K M)
      (underlyingComplex (CategoryTheory.Sheaf.CommAlg.commRing O) X) k)
    (p : ℤ) (m : M.X p) : Cochain K X (p + k) :=
  Cochain.mk fun q n h ↦
    (SheafOfModules.fullyFaithfulForget
      (CategoryTheory.Sheaf.CommAlg.ring O)).preimage
        (tmulPresheaf K M p q m ≫ f.v (p + q) n (curryDegree p q k n h))

/-- Homogeneous currying in one fixed degree of the right DG module. -/
@[stacks 09LY "linear component of arbitrary-ring sectionwise currying"]
def curryComponent (K : Complex.{r, u, v, w, max u z} O) (M : Modules K)
    (X : Complex.{r, u, v, w, max u z} O) {k : ℤ}
    (f : Cochain (presheafComplex K M)
      (underlyingComplex (CategoryTheory.Sheaf.CommAlg.commRing O) X) k)
    (p : ℤ) : M.X p →ₗ[R] (representableModule K X).X (p + k) where
  toFun := curryCochain K M X f p
  map_add' := sorry
  map_smul' := sorry

/-- Curry a homogeneous map from the sectionwise tensor presheaf complex. -/
@[stacks 09LY "arbitrary-ring homogeneous tensor-representable currying"]
def curry (K : Complex.{r, u, v, w, max u z} O) (M : Modules K)
    (X : Complex.{r, u, v, w, max u z} O) {k : ℤ}
    (f : Cochain (presheafComplex K M)
      (underlyingComplex (CategoryTheory.Sheaf.CommAlg.commRing O) X) k) :
    DifferentialGradedModule.GradedHom (endDGA K) M (representableModule K X) k :=
  ⟨curryComponent K M X f, sorry⟩

/-- Reassociation of source and target degrees in sectionwise homogeneous uncurrying. -/
@[stacks 09LY "degree reassociation for arbitrary-ring uncurrying"]
theorem uncurryDegree (p q k : ℤ) : q + (p + k) = (p + q) + k := sorry

/-- Evaluation of homogeneous uncurrying on two homogeneous elements over one site object. -/
@[stacks 09LY "evaluation of arbitrary-ring sectionwise uncurrying"]
def uncurryValue (K : Complex.{r, u, v, w, max u z} O) (M : Modules K)
    (X : Complex.{r, u, v, w, max u z} O) {k : ℤ}
    (g : DifferentialGradedModule.GradedHom (endDGA K) M (representableModule K X) k)
    (p q : ℤ) (U : Cᵒᵖ) (m : M.X p) (x : (sectionModule K U).X q) :
    Section X U ((p + q) + k) :=
  ((((g p m : Cochain K X (p + k)).v q ((p + q) + k)
    (uncurryDegree p q k)).val.app U).hom x)

/-- The degree-`k` sectionwise pairing obtained by evaluating a homogeneous representable-module
map on local sections. -/
@[stacks 09LY "arbitrary-ring sectionwise uncurrying pairing"]
def uncurryPairing (K : Complex.{r, u, v, w, max u z} O) (M : Modules K)
    (X : Complex.{r, u, v, w, max u z} O) {k : ℤ}
    (g : DifferentialGradedModule.GradedHom (endDGA K) M (representableModule K X) k)
    (U : Cᵒᵖ) :
    DifferentialGradedModule.TensorProduct.GradedPairing M (sectionModule K U)
      (sectionModule X U).toCochainComplex k :=
  fun p q ↦ ModuleCat.TensorProduct.lift R
    (LinearMap.mk₂ R (uncurryValue K M X g p q U) sorry sorry sorry sorry)

/-- The sectionwise evaluation pairing is balanced over the endomorphism DGA. -/
@[stacks 09LY "balanced arbitrary-ring sectionwise uncurrying pairing"]
theorem uncurryPairing_isBalanced
    (K : Complex.{r, u, v, w, max u z} O) (M : Modules K)
    (X : Complex.{r, u, v, w, max u z} O) {k : ℤ}
    (g : DifferentialGradedModule.GradedHom (endDGA K) M (representableModule K X) k)
    (U : Cᵒᵖ) :
    DifferentialGradedModule.TensorProduct.GradedIsBalanced M (sectionModule K U)
      (uncurryPairing K M X g U) := sorry

/-- Homogeneous uncurrying in one total degree as a morphism of module presheaves. -/
@[stacks 09LY "term of arbitrary-ring sectionwise uncurrying"]
def uncurryTerm (K : Complex.{r, u, v, w, max u z} O) (M : Modules K)
    (X : Complex.{r, u, v, w, max u z} O) {k : ℤ}
    (g : DifferentialGradedModule.GradedHom (endDGA K) M (representableModule K X) k)
    (n : ℤ) : term K M n ⟶
      (underlyingComplex (CategoryTheory.Sheaf.CommAlg.commRing O) X).X (n + k) where
  app U := ModuleCat.ofHom
    { toFun := (DifferentialGradedModule.TensorProduct.gradedLift M (sectionModule K U)
          (uncurryPairing K M X g U) (uncurryPairing_isBalanced K M X g U)).v
        n (n + k) rfl
      map_add' := sorry
      map_smul' := sorry }
  naturality := sorry

/-- Uncurry a homogeneous map into the representable module to a cochain of module presheaves. -/
@[stacks 09LY "arbitrary-ring homogeneous tensor-representable uncurrying"]
def uncurry (K : Complex.{r, u, v, w, max u z} O) (M : Modules K)
    (X : Complex.{r, u, v, w, max u z} O) {k : ℤ}
    (g : DifferentialGradedModule.GradedHom (endDGA K) M (representableModule K X) k) :
    Cochain (presheafComplex K M)
      (underlyingComplex (CategoryTheory.Sheaf.CommAlg.commRing O) X) k :=
  Cochain.mk fun n _ h ↦
    uncurryTerm K M X g n ≫
      eqToHom (congrArg
        (fun i ↦ (underlyingComplex
          (CategoryTheory.Sheaf.CommAlg.commRing O) X).X i) h)

/-- Degree-`k` currying before sheafification, retaining the canonical integral linearity of
presheaf morphisms. -/
@[stacks 09LY "presheaf-level arbitrary-ring tensor-representable equivalence"]
def presheafHomEquiv (K : Complex.{r, u, v, w, max u z} O) (M : Modules K)
    (X : Complex.{r, u, v, w, max u z} O) (k : ℤ) :
    Cochain (presheafComplex K M)
        (underlyingComplex (CategoryTheory.Sheaf.CommAlg.commRing O) X) k ≃ₗ[ℤ]
      DifferentialGradedModule.GradedHom (endDGA K) M (representableModule K X) k where
  toFun := curry K M X
  invFun := uncurry K M X
  map_add' := sorry
  map_smul' := sorry
  left_inv := sorry
  right_inv := sorry

/-- Degree-`k` tensor-representable currying as an `R`-linear equivalence of homogeneous maps. -/
@[stacks 09LY "arbitrary-ring tensor-representable homogeneous Hom equivalence"]
def homEquiv (K : Complex.{r, u, v, w, max u z} O) (M : Modules K)
    (X : Complex.{r, u, v, w, max u z} O) (k : ℤ) :
    Cochain (obj K M) X k ≃ₗ[R]
      DifferentialGradedModule.GradedHom (endDGA K) M (representableModule K X) k where
  toFun f := curry K M X
    (cochainEquiv (CategoryTheory.Sheaf.CommAlg.commRing O)
      (presheafComplex K M) X k f)
  invFun g := (cochainEquiv (CategoryTheory.Sheaf.CommAlg.commRing O)
    (presheafComplex K M) X k).symm (uncurry K M X g)
  map_add' := sorry
  map_smul' := sorry
  left_inv := sorry
  right_inv := sorry

/-- Currying in every degree gives a morphism between the tensor and representable Hom
complexes. -/
@[stacks 09LY "forward arbitrary-ring tensor-representable Hom-complex map"]
def homComplexForward (K : Complex.{r, u, v, w, max u z} O) (M : Modules K)
    (X : Complex.{r, u, v, w, max u z} O) :
    DifferentialGradedCategory.homComplex (obj K M) X ⟶
      DifferentialGradedCategory.homComplex M (representableModule K X) where
  f k := ModuleCat.ofHom (homEquiv K M X k).toLinearMap
  comm' := sorry

/-- Uncurrying in every degree gives the inverse morphism between the representable and tensor
Hom complexes. -/
@[stacks 09LY "inverse arbitrary-ring tensor-representable Hom-complex map"]
def homComplexBackward (K : Complex.{r, u, v, w, max u z} O) (M : Modules K)
    (X : Complex.{r, u, v, w, max u z} O) :
    DifferentialGradedCategory.homComplex M (representableModule K X) ⟶
      DifferentialGradedCategory.homComplex (obj K M) X where
  f k := ModuleCat.ofHom (homEquiv K M X k).symm.toLinearMap
  comm' := sorry

/-- The homogeneous tensor-representable equivalence is an isomorphism of DG Hom complexes. -/
@[stacks 09LY "arbitrary-ring tensor-representable Hom-complex isomorphism"]
def homComplexIso (K : Complex.{r, u, v, w, max u z} O) (M : Modules K)
    (X : Complex.{r, u, v, w, max u z} O) :
    DifferentialGradedCategory.homComplex (obj K M) X ≅
      DifferentialGradedCategory.homComplex M (representableModule K X) where
  hom := homComplexForward K M X
  inv := homComplexBackward K M X
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The tensor-representable equivalence restricted to closed degree-zero morphisms. -/
@[stacks 09LY "arbitrary-ring tensor-representable closed Hom equivalence"]
def compHomEquiv (K : Complex.{r, u, v, w, max u z} O)
    (M : Comp R (Modules K))
    (X : Comp R (Complex.{r, u, v, w, max u z} O)) :
    ((tensorFunctor K).mapComp.obj M ⟶ X) ≃
      (M ⟶ (representableDgFunctor K).mapComp.obj X) where
  toFun f := ⟨homEquiv K M.obj X.obj 0 f.val, sorry⟩
  invFun g := ⟨(homEquiv K M.obj X.obj 0).symm g.val, sorry⟩
  left_inv := sorry
  right_inv := sorry

/-- Tensoring with `K` is left adjoint to the enriched representable functor on closed
degree-zero categories. -/
@[stacks 09LY "arbitrary-ring underived tensor-representable adjunction"]
def adjunction (K : Complex.{r, u, v, w, max u z} O) :
    (tensorFunctor K).mapComp ⊣ (representableDgFunctor K).mapComp :=
  Adjunction.mkOfHomEquiv
    { homEquiv := compHomEquiv K
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

/-- The Hom equivalence of the closed tensor-representable adjunction is currying. -/
@[stacks 09LY "Hom equivalence of the arbitrary-ring underived adjunction"]
theorem adjunction_homEquiv (K : Complex.{r, u, v, w, max u z} O)
    (M : Comp R (Modules K))
    (X : Comp R (Complex.{r, u, v, w, max u z} O)) :
    (adjunction K).homEquiv M X = compHomEquiv K M X := sorry

/-- Closed currying preserves the homotopy relation on tensor morphisms. -/
@[stacks 09LY "arbitrary-ring currying preserves homotopy"]
theorem homotopyForward_sound (K : Complex.{r, u, v, w, max u z} O)
    {M : Modules K} {X : Complex.{r, u, v, w, max u z} O}
    {f g : CompHom ((tensorFunctor K).obj M) X}
    (h : Homotopic ((tensorFunctor K).obj M) X f g) :
    Homotopic M (representableModule K X)
      (compHomEquiv K ⟨M⟩ ⟨X⟩ f) (compHomEquiv K ⟨M⟩ ⟨X⟩ g) := sorry

/-- Closed uncurrying preserves the homotopy relation on representable-module morphisms. -/
@[stacks 09LY "arbitrary-ring uncurrying preserves homotopy"]
theorem homotopyBackward_sound (K : Complex.{r, u, v, w, max u z} O)
    {M : Modules K} {X : Complex.{r, u, v, w, max u z} O}
    {f g : CompHom M (representableModule K X)}
    (h : Homotopic M (representableModule K X) f g) :
    Homotopic ((tensorFunctor K).obj M) X
      ((compHomEquiv K ⟨M⟩ ⟨X⟩).symm f)
      ((compHomEquiv K ⟨M⟩ ⟨X⟩).symm g) := sorry

/-- Currying on homotopy classes, defined by mapping closed representatives. -/
@[stacks 09LY "arbitrary-ring currying on homotopy classes"]
def homotopyForward (K : Complex.{r, u, v, w, max u z} O)
    {M : Modules K} {X : Complex.{r, u, v, w, max u z} O} :
    HomotopyClass ((tensorFunctor K).obj M) X →
      HomotopyClass M (representableModule K X) :=
  _root_.Quotient.map (compHomEquiv K ⟨M⟩ ⟨X⟩)
    (fun _ _ h ↦ homotopyForward_sound K h)

/-- Uncurrying on homotopy classes, defined by mapping closed representatives. -/
@[stacks 09LY "arbitrary-ring uncurrying on homotopy classes"]
def homotopyBackward (K : Complex.{r, u, v, w, max u z} O)
    {M : Modules K} {X : Complex.{r, u, v, w, max u z} O} :
    HomotopyClass M (representableModule K X) →
      HomotopyClass ((tensorFunctor K).obj M) X :=
  _root_.Quotient.map (compHomEquiv K ⟨M⟩ ⟨X⟩).symm
    (fun _ _ h ↦ homotopyBackward_sound K h)

/-- Tensor-representable currying as an equivalence on enriched homotopy-category morphisms. -/
@[stacks 09LY "arbitrary-ring tensor-representable homotopy Hom equivalence"]
def homotopyHomEquiv (K : Complex.{r, u, v, w, max u z} O)
    (M : DifferentialGradedCategory.K R (Modules K))
    (X : DifferentialGradedCategory.K R (Complex.{r, u, v, w, max u z} O)) :
    ((tensorFunctor K).mapK.obj M ⟶ X) ≃
      (M ⟶ (representableDgFunctor K).mapK.obj X) where
  toFun := homotopyForward K
  invFun := homotopyBackward K
  left_inv := sorry
  right_inv := sorry

/-- The explicit tensor-representable adjunction on enriched homotopy categories. -/
@[stacks 09LY "arbitrary-ring tensor-representable homotopy adjunction"]
def homotopyAdjunction (K : Complex.{r, u, v, w, max u z} O) :
    (tensorFunctor K).mapK ⊣ (representableDgFunctor K).mapK :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homotopyHomEquiv K
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

/-- The Hom equivalence of the homotopy adjunction is quotient-level currying. -/
@[stacks 09LY "Hom equivalence of the arbitrary-ring homotopy adjunction"]
theorem homotopyAdjunction_homEquiv
    (K : Complex.{r, u, v, w, max u z} O)
    (M : DifferentialGradedCategory.K R (Modules K))
    (X : DifferentialGradedCategory.K R (Complex.{r, u, v, w, max u z} O)) :
    (homotopyAdjunction K).homEquiv M X = homotopyHomEquiv K M X := sorry

section Checks

variable (K : Complex.{r, u, v, w, max u z} O)

#synth (tensorFunctor K).mapComp.Additive
#synth (tensorFunctor K).mapComp.Linear R
#synth (representableDgFunctor K).mapComp.Additive
#synth (representableDgFunctor K).mapComp.Linear R
#synth (tensorFunctor K).mapK.Additive
#synth (tensorFunctor K).mapK.Linear R
#synth (representableDgFunctor K).mapK.Additive
#synth (representableDgFunctor K).mapK.Linear R

end Checks

end SheafOfModules.CommAlg.TensorWithObject
