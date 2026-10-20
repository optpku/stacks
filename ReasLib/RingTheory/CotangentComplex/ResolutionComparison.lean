module

public import ReasLib.RingTheory.CotangentComplex.StandardTriangle
public import ReasLib.RingTheory.CotangentComplex.Functoriality
public import ReasLib.AlgebraicTopology.SimplicialObject.ModuleCochain
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Comparison of standard and tensor polynomial resolutions

Coefficient change and tensor inclusion compare the standard resolution with
tensor base changes of standard resolutions. Their differential complexes are
identified by the resulting quasi-isomorphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialObject
open AlgebraicTopology HomologicalComplex Algebra Algebra.PolynomialSite
open CommAlgCat.Over.Polynomial.Site
open CommRingCat.Under.CotangentComplex
open scoped TensorProduct

noncomputable section

universe u q

set_option backward.privateInPublic true

namespace Algebra.CotangentComplex

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

private def relativeQ (X : PolynomialTower A B C) : CommAlgCat X.P :=
  @CommAlgCat.of X.P _ X.Q _ X.algebraPQ

private def relativeB (X : PolynomialTower A B C) : CommAlgCat X.P :=
  @CommAlgCat.of X.P _ B _ X.toB.hom.toRingHom.toAlgebra

/-- Coefficient change commutes with functoriality of standard resolutions. -/
private theorem functorialitySquare_comm (n : SimplexCategoryᵒᵖ) :
    (standardTermRightHom (B := (CommRingCat.of A).mkUnder C)
      (B' := (CommRingCat.of B).mkUnder C)
      (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (RingHom.id C)) n).hom.comp
        (functorialityApp A B C n).hom.toRingHom =
    (functorialityApp B B C n).hom.toRingHom.comp
      (standardTermRightHom (B := (CommRingCat.of A).mkUnder B)
        (B' := (CommRingCat.of B).mkUnder B)
        (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (RingHom.id B)) n).hom :=
  sorry

private abbrev algebraPOnBarR (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    Algebra ((triple A B C n h_inj).P) (barQ B B C n h_inj) :=
  ((algebraMap B (barQ B B C n h_inj)).comp
    ((standardHom A B).app n).hom.toRingHom).toAlgebra

private def targetOverP (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) : CommAlgCat ((triple A B C n h_inj).P) :=
  @CommAlgCat.of ((triple A B C n h_inj).P) _ (barQ B B C n h_inj) _
    (algebraPOnBarR A B C n h_inj)

private def tensorLeftRingHom (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    standardQ A C n →+* barQ B B C n h_inj :=
  (Algebra.TensorProduct.includeLeftRingHom :
    relativeQ B B C (triple B B C n h_inj) →+*
      relativeQ B B C (triple B B C n h_inj) ⊗[(triple B B C n h_inj).P]
        relativeB B B C (triple B B C n h_inj)).comp
    (standardTermRightHom (B := (CommRingCat.of A).mkUnder C)
      (B' := (CommRingCat.of B).mkUnder C)
      (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (RingHom.id C)) n).hom

/-- The coefficient-changing tensor inclusion respects the source standard algebra. -/
private theorem barQToBarRAlg_left_commutes (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) (p : (triple A B C n h_inj).P) :
    tensorLeftRingHom A B C n h_inj
      (algebraMap ((triple A B C n h_inj).P) (relativeQ A B C (triple A B C n h_inj)) p) =
        algebraMap ((triple A B C n h_inj).P) (targetOverP A B C n h_inj) p :=
  sorry

private def tensorLeft (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    relativeQ A B C (triple A B C n h_inj) →ₐ[(triple A B C n h_inj).P]
      targetOverP A B C n h_inj :=
  { tensorLeftRingHom A B C n h_inj with
    commutes' := barQToBarRAlg_left_commutes A B C n h_inj }

/-- The right tensor inclusion respects the augmentation of the source standard algebra. -/
private theorem barQToBarRAlg_right_commutes (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) (p : (triple A B C n h_inj).P) :
    algebraMap B (barQ B B C n h_inj)
      (algebraMap ((triple A B C n h_inj).P) (relativeB A B C (triple A B C n h_inj)) p) =
        algebraMap ((triple A B C n h_inj).P) (targetOverP A B C n h_inj) p :=
  sorry

private def tensorRight (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    relativeB A B C (triple A B C n h_inj) →ₐ[(triple A B C n h_inj).P]
      targetOverP A B C n h_inj :=
  { (algebraMap B (barQ B B C n h_inj)) with
    commutes' := barQToBarRAlg_right_commutes A B C n h_inj }

private def tensorComparisonRingHom (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    barQ A B C n h_inj →+* barQ B B C n h_inj :=
  (Algebra.TensorProduct.productMap (tensorLeft A B C n h_inj)
    (tensorRight A B C n h_inj)).toRingHom

/-- The tensor comparison is linear for the canonical right action of the intermediate ring. -/
private theorem barQToBarRAlg_commutes (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) (b : B) :
    tensorComparisonRingHom A B C n h_inj (algebraMap B (barQ A B C n h_inj) b) =
      algebraMap B (barQ B B C n h_inj) b :=
  sorry

/-- Coefficient change and the identity on the right factor induce a map of tensor algebras. -/
def barQToBarRAlg (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    (barQOver A B C n h_inj).obj.left →ₐ[B] (barQOver B B C n h_inj).obj.left :=
  { tensorComparisonRingHom A B C n h_inj with
    commutes' := barQToBarRAlg_commutes A B C n h_inj }

/-- The tensor comparison changes coefficients in the left factor and fixes the right factor. -/
theorem barQToBarRAlg_tmul (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C))
    (x : relativeQ A B C (triple A B C n h_inj))
    (b : relativeB A B C (triple A B C n h_inj)) :
    barQToBarRAlg A B C n h_inj (x ⊗ₜ[(triple A B C n h_inj).P] b) =
      (show relativeQ B B C (triple B B C n h_inj) from
        (standardTermRightHom (B := (CommRingCat.of A).mkUnder C)
          (B' := (CommRingCat.of B).mkUnder C)
          (CommRingCat.ofHom (algebraMap A B))
          (CommRingCat.ofHom (RingHom.id C)) n).hom x) ⊗ₜ[(triple B B C n h_inj).P]
        (show relativeB B B C (triple B B C n h_inj) from b) := by
  change (_ ⊗ₜ[(triple B B C n h_inj).P] (1 : relativeB B B C (triple B B C n h_inj))) *
    ((1 : relativeQ B B C (triple B B C n h_inj)) ⊗ₜ[(triple B B C n h_inj).P] _) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rfl

/-- The over-`C` triangle of `barQToBarRAlg`. -/
private theorem barQToBarROver_w (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    CommAlgCat.ofHom (barQToBarRAlg A B C n h_inj) ≫ (barQOver B B C n h_inj).obj.hom =
      (barQOver A B C n h_inj).obj.hom :=
  sorry

/-- The morphism of polynomial `B`-algebras over `C` from `Q̄_n` to `R̄_n`. -/
def barQToBarROver (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    barQOver A B C n h_inj ⟶ barQOver B B C n h_inj :=
  ObjectProperty.homMk
    (Over.homMk (CommAlgCat.ofHom (barQToBarRAlg A B C n h_inj))
      (barQToBarROver_w A B C n h_inj))

/-- The canonical simplicial `B`-algebra map `Q̄_• ⟶ R̄_•`. -/
def barQToBarR (h_inj : Function.Injective (algebraMap B C)) :
    barQSimplicial A B C h_inj ⟶ barQSimplicial B B C h_inj where
  app n := (barQToBarROver A B C n h_inj).hom.left
  naturality _ _ _ := sorry

/-- Components of `barQToBarR` are the left morphisms of `barQToBarROver`. -/
theorem barQToBarR_app (h_inj : Function.Injective (algebraMap B C))
    (n : SimplexCategoryᵒᵖ) :
    (barQToBarR A B C h_inj).app n = (barQToBarROver A B C n h_inj).hom.left :=
  rfl

/-- The polynomial `B`-algebra arrow `R_n ⟶ C` of the standard resolution. -/
private abbrev standardROver (n : SimplexCategoryᵒᵖ) : PolynomialOver B C :=
  (asPolynomialSimplicial (standardHom B C) (standard_isPolynomial B C)).obj n

/-- The left tensor inclusion respects the canonical base-ring actions. -/
private theorem standardToBarRAlg_commutes (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) (b : B) :
    (Algebra.TensorProduct.includeLeftRingHom :
      relativeQ B B C (triple B B C n h_inj) →+*
        relativeQ B B C (triple B B C n h_inj) ⊗[(triple B B C n h_inj).P]
          relativeB B B C (triple B B C n h_inj))
      (algebraMap B (standardROver B C n).obj.left b) =
        algebraMap B (barQ B B C n h_inj) b :=
  sorry

/-- The standard algebra maps to its tensor base change by the left tensor inclusion. -/
def standardToBarRAlg (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    (standardROver B C n).obj.left →ₐ[B] (barQOver B B C n h_inj).obj.left :=
  { (Algebra.TensorProduct.includeLeftRingHom :
      relativeQ B B C (triple B B C n h_inj) →+*
        relativeQ B B C (triple B B C n h_inj) ⊗[(triple B B C n h_inj).P]
          relativeB B B C (triple B B C n h_inj)) with
    commutes' := standardToBarRAlg_commutes B C n h_inj }

/-- The standard-to-tensor comparison sends an element to its tensor with one. -/
theorem standardToBarRAlg_apply (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C))
    (x : (standardROver B C n).obj.left) :
    standardToBarRAlg B C n h_inj x =
      (show relativeQ B B C (triple B B C n h_inj) from x) ⊗ₜ[(triple B B C n h_inj).P]
        (1 : relativeB B B C (triple B B C n h_inj)) := rfl

/-- The left tensor inclusion commutes with the augmentations. -/
private theorem standardToBarROver_w (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    (CommAlgCat.ofHom (X := (standardROver B C n).obj.left)
      (Y := (barQOver B B C n h_inj).obj.left) (standardToBarRAlg B C n h_inj)) ≫ (barQOver B B C n h_inj).obj.hom =
      (standardROver B C n).obj.hom :=
  sorry

/-- The morphism of polynomial `B`-algebras over `C` from `R_n` to `R̄_n`. -/
def standardToBarROver (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    standardROver B C n ⟶ barQOver B B C n h_inj :=
  ObjectProperty.homMk
    (Over.homMk ((CommAlgCat.ofHom (X := (standardROver B C n).obj.left)
      (Y := (barQOver B B C n h_inj).obj.left) (standardToBarRAlg B C n h_inj)))
      (standardToBarROver_w B C n h_inj))

/-- The simplicial `B`-algebra map `R_• ⟶ R̄_•`. -/
def standardToBarR (h_inj : Function.Injective (algebraMap B C)) :
    (standardAugmented B C).left ⟶ barQSimplicial B B C h_inj where
  app n := (standardToBarROver B C n h_inj).hom.left
  naturality _ _ _ := sorry

/-- Components of `standardToBarR` are the left morphisms of `standardToBarROver`. -/
theorem standardToBarR_app (h_inj : Function.Injective (algebraMap B C))
    (n : SimplexCategoryᵒᵖ) :
    (standardToBarR B C h_inj).app n = (standardToBarROver B C n h_inj).hom.left :=
  rfl

/-- The simplicial map on naive differentials induced by `Q̄_• ⟶ R̄_•`. -/
def omegaBarQToBarRSimplicial (h_inj : Function.Injective (algebraMap B C)) :
    omegaBarQSimplicial A B C h_inj ⟶ omegaBarQSimplicial B B C h_inj where
  app n := omegaSheafMap (barQToBarROver A B C n h_inj)
  naturality _ _ _ := sorry

/-- Components of `omegaBarQToBarRSimplicial` are `omegaSheafMap` of `barQToBarROver`. -/
theorem omegaBarQToBarRSimplicial_app (h_inj : Function.Injective (algebraMap B C))
    (n : SimplexCategoryᵒᵖ) :
    (omegaBarQToBarRSimplicial A B C h_inj).app n =
      omegaSheafMap (barQToBarROver A B C n h_inj) :=
  rfl

/-- The cochain map `Ω_{Q̄_•/B} ⊗ C ⟶ Ω_{R̄_•/B} ⊗ C` induced by `Q̄_• ⟶ R̄_•`. -/
def omegaBarQToBarR (h_inj : Function.Injective (algebraMap B C)) :
    omegaBarQCochain A B C h_inj ⟶ omegaBarQCochain B B C h_inj :=
  (simplicialModuleToCochain C).map (omegaBarQToBarRSimplicial A B C h_inj)

/-- `omegaBarQToBarR` is a quasi-isomorphism. -/
instance omegaBarQToBarR_quasiIso (h_inj : Function.Injective (algebraMap B C)) :
    QuasiIso (omegaBarQToBarR A B C h_inj) :=
  sorry

/-- Naive differentials `Ω_{R_•/B} ⊗_{R_•} C` of the standard resolution of `C` over `B`,
as a simplicial `C`-module. -/
abbrev omegaEvalSimplicial : SimplicialObject (ModuleCat.{u} C) :=
  asPolynomialSimplicial (standardHom B C) (standard_isPolynomial B C) ⋙ omegaSheafCov B C

/-- The cochain complex `Ω_{R_•/B} ⊗_{R_•} C` of naive differentials of the standard
resolution of `C` over `B`. -/
abbrev omegaEvalCochain : CochainComplex (ModuleCat.{u} C) ℤ :=
  (simplicialModuleToCochain C).obj (omegaEvalSimplicial B C)

/-- The simplicial map on naive differentials induced by `R_• ⟶ R̄_•`. -/
def omegaEvalToBarRSimplicial (h_inj : Function.Injective (algebraMap B C)) :
    omegaEvalSimplicial B C ⟶ omegaBarQSimplicial B B C h_inj where
  app n := omegaSheafMap (standardToBarROver B C n h_inj)
  naturality _ _ _ := sorry

/-- Components of `omegaEvalToBarRSimplicial` are `omegaSheafMap` of `standardToBarROver`. -/
theorem omegaEvalToBarRSimplicial_app (h_inj : Function.Injective (algebraMap B C))
    (n : SimplexCategoryᵒᵖ) :
    (omegaEvalToBarRSimplicial B C h_inj).app n =
      omegaSheafMap (standardToBarROver B C n h_inj) :=
  rfl

/-- The cochain map `Ω_{R_•/B} ⊗ C ⟶ Ω_{R̄_•/B} ⊗ C` induced by `R_• ⟶ R̄_•`. -/
def omegaEvalToBarR (h_inj : Function.Injective (algebraMap B C)) :
    omegaEvalCochain B C ⟶ omegaBarQCochain B B C h_inj :=
  (simplicialModuleToCochain C).map (omegaEvalToBarRSimplicial B C h_inj)

/-- `omegaEvalToBarR` is a quasi-isomorphism. -/
instance omegaEvalToBarR_quasiIso (h_inj : Function.Injective (algebraMap B C)) :
    QuasiIso (omegaEvalToBarR B C h_inj) :=
  sorry

/-- Composing `omegaBarQToBarR` with the inverse of `omegaEvalToBarR` identifies
`Ω_{Q̄_•/B} ⊗_{Q̄_•} C` with `Ω_{R_•/B} ⊗_{R_•} C` in `D(C)`. -/
instance barQ_iso_omegaEval (h_inj : Function.Injective (algebraMap B C))
    [HasDerivedCategory.{q} (ModuleCat.{u} C)] :
    IsIso (DerivedCategory.Q.map (omegaBarQToBarR A B C h_inj) ≫
      inv (DerivedCategory.Q.map (omegaEvalToBarR B C h_inj))) := by
  infer_instance

end Algebra.CotangentComplex
