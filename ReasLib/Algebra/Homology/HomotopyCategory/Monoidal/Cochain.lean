/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Functor
public import ReasLib.Algebra.Homology.HomotopyCategory.Monoidal
public import ReasLib.Algebra.Homology.HomotopyCategory.Monoidal.Functor

/-!
# Tensor comparison on homotopy categories of cochain complexes

This file specializes the generic two-variable localization API to the canonical tensor
comparison for a termwise monoidal additive functor on unbounded cochain complexes.  The generic
localization layer remains independent of totalization and coproduct-preservation hypotheses.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.Homotopy.Cochain

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  [MonoidalCategory C] [MonoidalCategory D]
  [SymmetricCategory C] [SymmetricCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
variable (F : C ⥤ D) [F.Additive] [F.Monoidal]
variable [∀ G₁ G₂ : GradedObject ℤ C, GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ C,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [∀ G₁ G₂ : GradedObject ℤ D, GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ D,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ D,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ D,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [Functor.Cochain.HasMappedTensorTotals F]
variable [HomotopyCategory.Koszul.TensorDescends (C := C)]
variable [HomotopyCategory.Koszul.TensorDescends (C := D)]

/-- The canonical cochain-complex tensor comparison descended to homotopy categories. -/
@[stacks 07A4 "canonical homotopy-category tensor comparison"]
noncomputable def tensorComparisonNatTrans :
    curriedTensorPre (F.mapHomotopyCategory (up ℤ)) ⟶
      curriedTensorPost (F.mapHomotopyCategory (up ℤ)) :=
  Homotopy.tensorComparisonNatTrans F
    (Functor.Cochain.tensorComparisonNatTrans F)

/-- The canonical tensor comparison on a pair of objects of the homotopy category. -/
noncomputable abbrev tensorComparison
    (K L : HomotopyCategory C (up ℤ)) :
    (F.mapHomotopyCategory (up ℤ)).obj K ⊗
        (F.mapHomotopyCategory (up ℤ)).obj L ⟶
      (F.mapHomotopyCategory (up ℤ)).obj (K ⊗ L) :=
  ((tensorComparisonNatTrans F).app K).app L

/-- The canonical cochain-complex unit isomorphism descended to homotopy categories. -/
@[stacks 07A4 "canonical homotopy-category unit isomorphism"]
noncomputable def unitIso :
    𝟙_ (HomotopyCategory D (up ℤ)) ≅
      (F.mapHomotopyCategory (up ℤ)).obj
        (𝟙_ (HomotopyCategory C (up ℤ))) :=
  Homotopy.unitIsoOfComp F (Functor.Cochain.unitIso F)

/-- On quotient representatives, the canonical homotopy-level tensor comparison is the quotient
of the cochain-complex comparison, conjugated by the factorization isomorphisms. -/
@[simp]
theorem tensorComparison_quotient (K L : CochainComplex C ℤ) :
    tensorComparison F
        ((HomotopyCategory.quotient C (up ℤ)).obj K)
        ((HomotopyCategory.quotient C (up ℤ)).obj L) =
      ((Homotopy.tensorPreFactors F).hom.app K).app L ≫
        (HomotopyCategory.quotient D (up ℤ)).map
          (Functor.Cochain.tensorComparison F K L) ≫
        ((Homotopy.tensorPostFactors F).inv.app K).app L := sorry

/-- The descended comparison on quotient representatives is invertible exactly when the
cochain-complex comparison is a homotopy equivalence. -/
@[stacks 07A4 "homotopy tensor comparison invertibility criterion"]
theorem tensorComparison_isIso_iff_homotopyEquivalence
    (K L : CochainComplex C ℤ) :
    IsIso (tensorComparison F
        ((HomotopyCategory.quotient C (up ℤ)).obj K)
        ((HomotopyCategory.quotient C (up ℤ)).obj L)) ↔
      HomologicalComplex.homotopyEquivalences D (up ℤ)
        (Functor.Cochain.tensorComparison F K L) := sorry

namespace TensorComparison

/-- The exact strongness condition for the canonical homotopy-level tensor comparison. -/
@[stacks 07A4 "invertible homotopy-category tensor comparison"]
abbrev IsInvertible : Prop :=
  ∀ K L : HomotopyCategory C (up ℤ), IsIso (Cochain.tensorComparison F K L)

end TensorComparison

/-- Naturality of the canonical homotopy-level tensor comparison in its left variable. -/
@[reassoc]
theorem tensorComparison_natural_left
    {K K' : HomotopyCategory C (up ℤ)} (f : K ⟶ K')
    (L : HomotopyCategory C (up ℤ)) :
    (F.mapHomotopyCategory (up ℤ)).map f ▷
          (F.mapHomotopyCategory (up ℤ)).obj L ≫
        tensorComparison F K' L =
      tensorComparison F K L ≫
        (F.mapHomotopyCategory (up ℤ)).map (f ▷ L) := sorry

/-- Naturality of the canonical homotopy-level tensor comparison in its right variable. -/
@[reassoc]
theorem tensorComparison_natural_right
    (K : HomotopyCategory C (up ℤ))
    {L L' : HomotopyCategory C (up ℤ)} (f : L ⟶ L') :
    (F.mapHomotopyCategory (up ℤ)).obj K ◁
          (F.mapHomotopyCategory (up ℤ)).map f ≫
        tensorComparison F K L' =
      tensorComparison F K L ≫
        (F.mapHomotopyCategory (up ℤ)).map (K ◁ f) := sorry

/-- The canonical homotopy-level tensor comparison respects associators. -/
theorem tensorComparison_associativity
    (K L M : HomotopyCategory C (up ℤ)) :
    tensorComparison F K L ▷
          (F.mapHomotopyCategory (up ℤ)).obj M ≫
        tensorComparison F (K ⊗ L) M ≫
          (F.mapHomotopyCategory (up ℤ)).map (α_ K L M).hom =
      (α_ ((F.mapHomotopyCategory (up ℤ)).obj K)
        ((F.mapHomotopyCategory (up ℤ)).obj L)
        ((F.mapHomotopyCategory (up ℤ)).obj M)).hom ≫
        (F.mapHomotopyCategory (up ℤ)).obj K ◁
          tensorComparison F L M ≫
        tensorComparison F K (L ⊗ M) := sorry

/-- The canonical homotopy-level unit and tensor comparisons respect the left unitor. -/
theorem tensorComparison_left_unitality
    (K : HomotopyCategory C (up ℤ)) :
    (λ_ ((F.mapHomotopyCategory (up ℤ)).obj K)).hom =
      (unitIso F).hom ▷ (F.mapHomotopyCategory (up ℤ)).obj K ≫
        tensorComparison F (𝟙_ (HomotopyCategory C (up ℤ))) K ≫
          (F.mapHomotopyCategory (up ℤ)).map (λ_ K).hom := sorry

/-- The canonical homotopy-level unit and tensor comparisons respect the right unitor. -/
theorem tensorComparison_right_unitality
    (K : HomotopyCategory C (up ℤ)) :
    (ρ_ ((F.mapHomotopyCategory (up ℤ)).obj K)).hom =
      (F.mapHomotopyCategory (up ℤ)).obj K ◁ (unitIso F).hom ≫
        tensorComparison F K (𝟙_ (HomotopyCategory C (up ℤ))) ≫
          (F.mapHomotopyCategory (up ℤ)).map (ρ_ K).hom := sorry

/-- `07A4:` The canonical homotopy tensor comparison as an isomorphism, from an explicit
invertibility certificate.  This is the non-instance owner for downstream constructions that
must not install a proof-local monoidal structure. -/
@[stacks 07A4 "homotopy tensor isomorphism from explicit invertibility"]
noncomputable def tensorIsoOf
    (h : TensorComparison.IsInvertible F)
    (K L : HomotopyCategory C (up ℤ)) :
    (F.mapHomotopyCategory (up ℤ)).obj K ⊗
        (F.mapHomotopyCategory (up ℤ)).obj L ≅
      (F.mapHomotopyCategory (up ℤ)).obj (K ⊗ L) :=
  @asIso _ _ _ _ (tensorComparison F K L) (h K L)

/-- `07A4:` The strong monoidal core determined by an explicit invertibility certificate for
the canonical descended cochain comparison. -/
@[stacks 07A4 "homotopy monoidal core from explicit invertibility"]
noncomputable def coreMonoidalOf
    (h : TensorComparison.IsInvertible F) :
    (F.mapHomotopyCategory (up ℤ)).CoreMonoidal where
  εIso := unitIso F
  μIso := tensorIsoOf F h
  μIso_hom_natural_left := tensorComparison_natural_left F
  μIso_hom_natural_right := fun K f ↦ tensorComparison_natural_right F K f
  associativity := tensorComparison_associativity F
  left_unitality := tensorComparison_left_unitality F
  right_unitality := tensorComparison_right_unitality F

section Strong

variable [h : TensorComparison.IsInvertible F]

/-- The canonical tensor comparison as an isomorphism, conditional exactly on its invertibility. -/
@[stacks 07A4 "canonical homotopy-category tensor isomorphism"]
noncomputable abbrev tensorIso
    (K L : HomotopyCategory C (up ℤ)) :
    (F.mapHomotopyCategory (up ℤ)).obj K ⊗
        (F.mapHomotopyCategory (up ℤ)).obj L ≅
      (F.mapHomotopyCategory (up ℤ)).obj (K ⊗ L) :=
  tensorIsoOf F h K L

/-- The strong monoidal core determined by the canonical descended cochain comparison. -/
@[stacks 07A4 "canonical homotopy-category monoidal core"]
noncomputable def coreMonoidal :
    (F.mapHomotopyCategory (up ℤ)).CoreMonoidal :=
  coreMonoidalOf F h

/-- The canonical strong monoidal structure on the induced homotopy-category functor. -/
@[stacks 07A4 "canonical homotopy-category monoidal functor", implicit_reducible]
noncomputable instance monoidal :
    (F.mapHomotopyCategory (up ℤ)).Monoidal :=
  (coreMonoidal F).toMonoidal

/-- The hom of the canonical tensor isomorphism is the canonical tensor comparison. -/
@[simp]
theorem tensorIso_hom (K L : HomotopyCategory C (up ℤ)) :
    (tensorIso F K L).hom = tensorComparison F K L := sorry

end Strong

end CategoryTheory.Functor.Homotopy.Cochain
