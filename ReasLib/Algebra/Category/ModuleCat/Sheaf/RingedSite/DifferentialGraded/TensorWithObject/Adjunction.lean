module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.DifferentialGraded.Representable.Functor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject

/-!
# Tensor-representable adjunction on a ringed site

This file constructs homogeneous currying and uncurrying for the explicit sectionwise relative
tensor functor.  The construction first uses the universal property of module sheafification and
then descends a sectionwise bilinear evaluation through the relative tensor quotient.  The
resulting degreewise linear equivalence is packaged as an isomorphism of Hom complexes, an
adjunction on closed degree-zero categories, and an adjunction on DG homotopy categories.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open CochainComplex.HomComplex
open DifferentialGradedCategory
open HomologicalComplex
open scoped DifferentialGradedCategory
open SheafOfModules.RingedSite.ModuleSheafification

namespace SheafOfModules.RingedSite.TensorWithObject

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {O : Sheaf J CommRingCat.{max u v}}

/-- Pure tensor formation after fixing a homogeneous right-module element, as a morphism of
module presheaves in the remaining section variable. -/
@[stacks 09LY "pure tensor map used by currying"]
def tmulPresheaf (K : Complex (J := J) (O := O)) (M : Modules K)
    (p q : ℤ) (m : M.X p) : (K.X q).val ⟶ term K M (p + q) where
  app U := ModuleCat.ofHom
    { toFun := fun x ↦
        DifferentialGradedModule.TensorProduct.tmul M (sectionModule K U) m x
      map_add' := sorry
      map_smul' := sorry }
  naturality := sorry

/-- Reassociation of the target degree in sectionwise homogeneous currying. -/
@[stacks 09LY "degree reassociation for currying"]
theorem curryDegree (p q k r : ℤ) (h : q + (p + k) = r) :
    (p + q) + k = r := sorry

/-- Curry a presheaf cochain after fixing a homogeneous element of the right DG module. -/
@[stacks 09LY "elementwise homogeneous currying"]
def curryCochain (K : Complex (J := J) (O := O)) (M : Modules K)
    (X : Complex (J := J) (O := O)) {k : ℤ}
    (f : Cochain (presheafComplex K M) (underlyingComplex O X) k)
    (p : ℤ) (m : M.X p) : Cochain K X (p + k) :=
  Cochain.mk fun q r h ↦
    (SheafOfModules.fullyFaithfulForget (ringSheaf J O)).preimage
      (tmulPresheaf K M p q m ≫ f.v (p + q) r (curryDegree p q k r h))

/-- Homogeneous currying in one fixed degree of the right DG module. -/
@[stacks 09LY "degreewise homogeneous currying"]
def curryComponent (K : Complex (J := J) (O := O)) (M : Modules K)
    (X : Complex (J := J) (O := O)) {k : ℤ}
    (f : Cochain (presheafComplex K M) (underlyingComplex O X) k)
    (p : ℤ) : M.X p →ₗ[ℤ] (representableModule K X).X (p + k) where
  toFun := curryCochain K M X f p
  map_add' := sorry
  map_smul' := sorry

/-- Curry a homogeneous map from the sectionwise tensor presheaf complex. -/
@[stacks 09LY "homogeneous tensor-representable currying"]
def curry (K : Complex (J := J) (O := O)) (M : Modules K)
    (X : Complex (J := J) (O := O)) {k : ℤ}
    (f : Cochain (presheafComplex K M) (underlyingComplex O X) k) :
    DifferentialGradedModule.GradedHom (endDGA K) M (representableModule K X) k :=
  ⟨curryComponent K M X f, sorry⟩

/-- Reassociation of source and target degrees in sectionwise homogeneous uncurrying. -/
@[stacks 09LY "degree reassociation for uncurrying"]
theorem uncurryDegree (p q k : ℤ) : q + (p + k) = (p + q) + k := sorry

/-- Evaluation of homogeneous uncurrying on two homogeneous elements over one site object. -/
@[stacks 09LY "elementwise homogeneous uncurrying"]
def uncurryValue (K : Complex (J := J) (O := O)) (M : Modules K)
    (X : Complex (J := J) (O := O)) {k : ℤ}
    (g : DifferentialGradedModule.GradedHom (endDGA K) M (representableModule K X) k)
    (p q : ℤ) (U : Cᵒᵖ) (m : M.X p) (x : (sectionModule K U).X q) :
    Section X U ((p + q) + k) :=
  ((((g p m : Cochain K X (p + k)).v q ((p + q) + k)
    (uncurryDegree p q k)).val.app U).hom x)

/-- The degree-`k` sectionwise pairing obtained by evaluating a homogeneous representable-module
map on local sections. -/
@[stacks 09LY "sectionwise uncurrying pairing"]
def uncurryPairing (K : Complex (J := J) (O := O)) (M : Modules K)
    (X : Complex (J := J) (O := O)) {k : ℤ}
    (g : DifferentialGradedModule.GradedHom (endDGA K) M (representableModule K X) k)
    (U : Cᵒᵖ) :
    DifferentialGradedModule.TensorProduct.GradedPairing M (sectionModule K U)
      (sectionModule X U).toCochainComplex k :=
  fun p q ↦ ModuleCat.TensorProduct.lift ℤ
    (LinearMap.mk₂ ℤ (uncurryValue K M X g p q U) sorry sorry sorry sorry)

/-- The sectionwise evaluation pairing is balanced over the endomorphism DGA. -/
@[stacks 09LY "balancedness of the uncurrying pairing"]
theorem uncurryPairing_isBalanced (K : Complex (J := J) (O := O)) (M : Modules K)
    (X : Complex (J := J) (O := O)) {k : ℤ}
    (g : DifferentialGradedModule.GradedHom (endDGA K) M (representableModule K X) k)
    (U : Cᵒᵖ) :
    DifferentialGradedModule.TensorProduct.GradedIsBalanced M (sectionModule K U)
      (uncurryPairing K M X g U) := sorry

/-- Homogeneous uncurrying in one total degree as a morphism of module presheaves. -/
@[stacks 09LY "degreewise uncurrying morphism"]
def uncurryTerm (K : Complex (J := J) (O := O)) (M : Modules K)
    (X : Complex (J := J) (O := O)) {k : ℤ}
    (g : DifferentialGradedModule.GradedHom (endDGA K) M (representableModule K X) k)
    (n : ℤ) : term K M n ⟶ (underlyingComplex O X).X (n + k) where
  app U := ModuleCat.ofHom
    { toFun := (DifferentialGradedModule.TensorProduct.gradedLift M (sectionModule K U)
          (uncurryPairing K M X g U) (uncurryPairing_isBalanced K M X g U)).v
        n (n + k) rfl
      map_add' := sorry
      map_smul' := sorry }
  naturality := sorry

/-- Uncurry a homogeneous map into the representable module to a cochain of module presheaves. -/
@[stacks 09LY "homogeneous tensor-representable uncurrying"]
def uncurry (K : Complex (J := J) (O := O)) (M : Modules K)
    (X : Complex (J := J) (O := O)) {k : ℤ}
    (g : DifferentialGradedModule.GradedHom (endDGA K) M (representableModule K X) k) :
    Cochain (presheafComplex K M) (underlyingComplex O X) k :=
  Cochain.mk fun n _ h ↦
    uncurryTerm K M X g n ≫
      eqToHom (congrArg (fun i ↦ (underlyingComplex O X).X i) h)

/-- Degree-`k` currying for the sectionwise tensor presheaf as a linear equivalence. -/
@[stacks 09LY "presheaf-level tensor-representable Hom equivalence"]
def presheafHomEquiv (K : Complex (J := J) (O := O)) (M : Modules K)
    (X : Complex (J := J) (O := O)) (k : ℤ) :
    Cochain (presheafComplex K M) (underlyingComplex O X) k ≃ₗ[ℤ]
      DifferentialGradedModule.GradedHom (endDGA K) M (representableModule K X) k where
  toFun := curry K M X
  invFun := uncurry K M X
  map_add' := sorry
  map_smul' := sorry
  left_inv := sorry
  right_inv := sorry

/-- Degree-`k` tensor-representable currying as an integral linear equivalence of homogeneous
maps. -/
@[stacks 09LY "tensor-representable homogeneous Hom equivalence"]
def homEquiv (K : Complex (J := J) (O := O)) (M : Modules K)
    (X : Complex (J := J) (O := O)) (k : ℤ) :
    Cochain (obj K M) X k ≃ₗ[ℤ]
      DifferentialGradedModule.GradedHom (endDGA K) M (representableModule K X) k :=
  (cochainEquiv O (presheafComplex K M) X k).trans
    (presheafHomEquiv K M X k)

/-- Currying in every degree gives a morphism between the tensor and representable Hom
complexes. -/
@[stacks 09LY "forward map of the tensor-representable Hom complex isomorphism"]
def homComplexForward (K : Complex (J := J) (O := O)) (M : Modules K)
    (X : Complex (J := J) (O := O)) :
    DifferentialGradedCategory.homComplex (obj K M) X ⟶
      DifferentialGradedCategory.homComplex M (representableModule K X) where
  f k := ModuleCat.ofHom (homEquiv K M X k).toLinearMap
  comm' := sorry

/-- Uncurrying in every degree gives the inverse morphism between the representable and tensor
Hom complexes. -/
@[stacks 09LY "backward map of the tensor-representable Hom complex isomorphism"]
def homComplexBackward (K : Complex (J := J) (O := O)) (M : Modules K)
    (X : Complex (J := J) (O := O)) :
    DifferentialGradedCategory.homComplex M (representableModule K X) ⟶
      DifferentialGradedCategory.homComplex (obj K M) X where
  f k := ModuleCat.ofHom (homEquiv K M X k).symm.toLinearMap
  comm' := sorry

/-- The homogeneous tensor-representable equivalence is an isomorphism of DG Hom complexes. -/
@[stacks 09LY "underived tensor-representable Hom complex isomorphism"]
def homComplexIso (K : Complex (J := J) (O := O)) (M : Modules K)
    (X : Complex (J := J) (O := O)) :
    DifferentialGradedCategory.homComplex (obj K M) X ≅
      DifferentialGradedCategory.homComplex M (representableModule K X) where
  hom := homComplexForward K M X
  inv := homComplexBackward K M X
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The tensor-representable equivalence restricted to closed degree-zero morphisms. -/
@[stacks 09LY "tensor-representable closed Hom equivalence"]
def compHomEquiv (K : Complex (J := J) (O := O))
    (M : Comp ℤ (Modules K)) (X : Comp ℤ (Complex (J := J) (O := O))) :
    ((tensorFunctor K).mapComp.obj M ⟶ X) ≃
      (M ⟶ (representableDgFunctor K).mapComp.obj X) where
  toFun f := ⟨homEquiv K M.obj X.obj 0 f.val, sorry⟩
  invFun g := ⟨(homEquiv K M.obj X.obj 0).symm g.val, sorry⟩
  left_inv := sorry
  right_inv := sorry

/-- Tensoring with `K` is left adjoint to the enriched representable functor on closed
degree-zero categories. -/
@[stacks 09LY "underived tensor-representable adjunction"]
def adjunction (K : Complex (J := J) (O := O)) :
    (tensorFunctor K).mapComp ⊣ (representableDgFunctor K).mapComp :=
  Adjunction.mkOfHomEquiv
    { homEquiv := compHomEquiv K
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

/-- The Hom equivalence of the concrete closed tensor-representable adjunction is currying. -/
@[stacks 09LY "closed adjunction Hom equivalence"]
theorem adjunction_homEquiv (K : Complex (J := J) (O := O))
    (M : Comp ℤ (Modules K)) (X : Comp ℤ (Complex (J := J) (O := O))) :
    (adjunction K).homEquiv M X = compHomEquiv K M X := sorry

/-- Closed currying preserves the homotopy relation on tensor morphisms. -/
@[stacks 09LY "currying respects homotopy"]
theorem homotopyForward_sound (K : Complex (J := J) (O := O))
    {M : Modules K} {X : Complex (J := J) (O := O)}
    {f g : CompHom ((tensorFunctor K).obj M) X}
    (h : Homotopic ((tensorFunctor K).obj M) X f g) :
    Homotopic M (representableModule K X)
      (compHomEquiv K ⟨M⟩ ⟨X⟩ f) (compHomEquiv K ⟨M⟩ ⟨X⟩ g) := sorry

/-- Closed uncurrying preserves the homotopy relation on representable-module morphisms. -/
@[stacks 09LY "uncurrying respects homotopy"]
theorem homotopyBackward_sound (K : Complex (J := J) (O := O))
    {M : Modules K} {X : Complex (J := J) (O := O)}
    {f g : CompHom M (representableModule K X)}
    (h : Homotopic M (representableModule K X) f g) :
    Homotopic ((tensorFunctor K).obj M) X
      ((compHomEquiv K ⟨M⟩ ⟨X⟩).symm f) ((compHomEquiv K ⟨M⟩ ⟨X⟩).symm g) := sorry

/-- Currying on homotopy classes, defined by mapping explicit closed representatives. -/
@[stacks 09LY "currying on homotopy classes"]
def homotopyForward (K : Complex (J := J) (O := O))
    {M : Modules K} {X : Complex (J := J) (O := O)} :
    HomotopyClass ((tensorFunctor K).obj M) X →
      HomotopyClass M (representableModule K X) :=
  _root_.Quotient.map (compHomEquiv K ⟨M⟩ ⟨X⟩)
    (fun _ _ h ↦ homotopyForward_sound K h)

/-- Uncurrying on homotopy classes, defined by mapping explicit closed representatives. -/
@[stacks 09LY "uncurrying on homotopy classes"]
def homotopyBackward (K : Complex (J := J) (O := O))
    {M : Modules K} {X : Complex (J := J) (O := O)} :
    HomotopyClass M (representableModule K X) →
      HomotopyClass ((tensorFunctor K).obj M) X :=
  _root_.Quotient.map (compHomEquiv K ⟨M⟩ ⟨X⟩).symm
    (fun _ _ h ↦ homotopyBackward_sound K h)

/-- Tensor-representable currying as an equivalence on DG homotopy-category morphisms. -/
@[stacks 09LY "tensor-representable homotopy Hom equivalence"]
def homotopyHomEquiv (K : Complex (J := J) (O := O))
    (M : DifferentialGradedCategory.K ℤ (Modules K))
    (X : DifferentialGradedCategory.K ℤ (Complex (J := J) (O := O))) :
    ((tensorFunctor K).mapK.obj M ⟶ X) ≃
      (M ⟶ (representableDgFunctor K).mapK.obj X) where
  toFun := homotopyForward K
  invFun := homotopyBackward K
  left_inv := sorry
  right_inv := sorry

/-- The explicit tensor-representable adjunction on DG homotopy categories. -/
@[stacks 09LY "tensor-representable adjunction on homotopy categories"]
def homotopyAdjunction (K : Complex (J := J) (O := O)) :
    (tensorFunctor K).mapK ⊣ (representableDgFunctor K).mapK :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homotopyHomEquiv K
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

/-- The Hom equivalence of the homotopy-category adjunction is quotient-level currying. -/
@[stacks 09LY "homotopy adjunction Hom equivalence"]
theorem homotopyAdjunction_homEquiv (K : Complex (J := J) (O := O))
    (M : DifferentialGradedCategory.K ℤ (Modules K))
    (X : DifferentialGradedCategory.K ℤ (Complex (J := J) (O := O))) :
    (homotopyAdjunction K).homEquiv M X = homotopyHomEquiv K M X := sorry

end SheafOfModules.RingedSite.TensorWithObject
