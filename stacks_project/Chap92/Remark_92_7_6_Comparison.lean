module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.RingTheory.TensorProduct.Maps
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import stacks_project.Chap92.Lemma_92_10_1_Maps
public import stacks_project.Chap92.Remark_92_7_5

/-!
# Canonical comparison of `Q̄_•` with the standard resolution of `C` over `B`

For ring maps `A → B → C` with `B → C` injective, functoriality of standard
resolutions supplies maps `Q̄_• → R̄_•` and `R_• → R̄_•`. The induced maps on
`Ω_{−/B} ⊗ C` are quasi-isomorphisms, and their derived-category composite
identifies `Ω_{Q̄_•/B} ⊗_{Q̄_•} C` with `Ω_{R_•/B} ⊗_{R_•} C`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SimplicialObject
open Opposite
open AlgebraicTopology
open HomologicalComplex
open ComplexShape
open Algebra
open Algebra.PolynomialSite
open RingedSite.Cotangent.PolynomialTriple
open CommAlgCat.Over.Polynomial.Site
open CategoryTheory.CommRingCat.Under.PolynomialResolution
open CommRingCat.Under.CotangentComplex
open scoped Simplicial TensorProduct Algebra.TensorProduct.Right

noncomputable section

universe u q

namespace Algebra.CotangentComplex

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/-- The standard-resolution term `S_n` of `B` over `B`. -/
abbrev standardS (n : SimplexCategoryᵒᵖ) : Type u :=
  standardP B B n

/-- The standard-resolution term `R_n` of `C` over `B`. -/
abbrev standardR (n : SimplexCategoryᵒᵖ) : Type u :=
  standardQ B C n

/-- The functoriality map `S_n ⟶ R_n` of standard resolutions of `B` and `C` over `B`. -/
abbrev functorialitySR (n : SimplexCategoryᵒᵖ) :
    (standardAugmented B B).left.obj n ⟶ (standardAugmented B C).left.obj n :=
  functorialityApp B B C n

/-- If `B → C` is injective, then each standard-resolution term `R_n` is a polynomial
algebra over `S_n`. -/
theorem isPolynomial_standardR_over_standardS (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    IsPolynomial (standardS B n) (standardR B C n) :=
  sorry

/-- The functoriality map of standard-resolution terms induced by `A → B` on the
resolution of `C`. -/
def functorialityQR (n : SimplexCategoryᵒᵖ) :
    (standardTerm (CommRingCat.of A) ((CommRingCat.of A).mkUnder C) n).right ⟶
      (standardTerm (CommRingCat.of B) ((CommRingCat.of B).mkUnder C) n).right :=
  iterateRightHom (CommRingCat.ofHom (algebraMap A B))
    (CommRingCat.ofHom (RingHom.id C)) (n.unop.len + 1)

/-- The functoriality ring map `Q_n →+* R_n` induced by `A → B`. -/
def functorialityQRHom (n : SimplexCategoryᵒᵖ) :
    standardQ A C n →+* standardQ B C n :=
  (functorialityQR A B C n).hom

/-- Applying `functorialityQRHom` recovers the iterate ring map on carriers. -/
theorem functorialityQRHom_apply (n : SimplexCategoryᵒᵖ) (x : standardQ A C n) :
    functorialityQRHom A B C n x = (functorialityQR A B C n).hom x :=
  sorry

/-- The functoriality square `Q_• → R_•` over `P_• → S_•` commutes. -/
theorem functorialitySquare_comm (n : SimplexCategoryᵒᵖ) :
    (functorialityQRHom A B C n).comp (functorialityApp A B C n).hom.toRingHom =
      (functorialitySR B C n).hom.toRingHom.comp (functorialityQRHom A B B n) :=
  sorry

/-- The polynomial `B`-algebra arrow `R̄_n = R_n ⊗[S_n] B ⟶ C`. -/
abbrev barROver (n : SimplexCategoryᵒᵖ) (h_inj : Function.Injective (algebraMap B C)) :
    PolynomialOver B C :=
  barQOver B B C n h_inj

/-- The auxiliary algebra `R̄_n = R_n ⊗[S_n] B`. -/
abbrev barR (n : SimplexCategoryᵒᵖ) (h_inj : Function.Injective (algebraMap B C)) :
    Type u :=
  barQ B B C n h_inj

/-- The simplicial polynomial `B`-algebra `R̄_•`. -/
abbrev barRSimplicial (h_inj : Function.Injective (algebraMap B C)) :
    SimplicialObject (CommAlgCat.{u} B) :=
  barQSimplicial B B C h_inj

/-- The augmentation `R̄_• ⟶ C` of simplicial `B`-algebras. -/
abbrev barRHom (h_inj : Function.Injective (algebraMap B C)) :=
  barQHom B B C h_inj

/-- Each `R̄_n` is a polynomial `B`-algebra. -/
theorem isPolynomial_barR (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    IsPolynomial B (barR B C n h_inj) :=
  sorry

/-- The auxiliary algebra `R̄_•` is a polynomial simplicial resolution of `C` over `B`. -/
theorem isResolution_barRHom (h_inj : Function.Injective (algebraMap B C)) :
    IsResolution (barRHom B C h_inj) :=
  sorry

/-- Being a resolution of `C` over `B` is equivalent to the degreewise polynomial
condition on `R̄_n` together with the trivial Kan fibration condition on `barRHom`. -/
theorem isResolution_barRHom_iff (h_inj : Function.Injective (algebraMap B C)) :
    IsResolution (barRHom B C h_inj) ↔
      (∀ n, IsPolynomial B ((barRSimplicial B C h_inj).obj n)) ∧
        SSet.modelCategoryQuillen.I.rlp (underlyingSSetMap (barRHom B C h_inj)) :=
  sorry

/-- The `P_n`-algebra structure on `R_n ⊗[S_n] B` via `P_n → B`. -/
@[reducible] def algebraPOnBarR (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C))
    [Algebra (triple B B C n h_inj).P B]
    [Algebra B ((triple B B C n h_inj).Q ⊗[(triple B B C n h_inj).P] B)]
    [Algebra (triple A B C n h_inj).P B] :
    Algebra (triple A B C n h_inj).P
      ((triple B B C n h_inj).Q ⊗[(triple B B C n h_inj).P] B) :=
  RingHom.toAlgebra
    ((algebraMap B ((triple B B C n h_inj).Q ⊗[(triple B B C n h_inj).P] B)).comp
      (algebraMap (triple A B C n h_inj).P B))

/-- The `B`-algebra map `Q̄_n ⟶ R̄_n` induced by the functoriality square. -/
def barQToBarRAlg (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :=
  @go n h_inj
    (algebraPB (triple A B C n h_inj)) (algebraPB (triple B B C n h_inj))
    (triple B B C n h_inj).algebraPQ
    (@Algebra.TensorProduct.rightAlgebra (triple A B C n h_inj).P
      (triple A B C n h_inj).Q B _ _ _ _ (algebraPB (triple A B C n h_inj)))
    (@Algebra.TensorProduct.rightAlgebra (triple B B C n h_inj).P
      (triple B B C n h_inj).Q B _ _ _ _ (algebraPB (triple B B C n h_inj)))
    (@algebraPOnBarR A B C _ _ _ _ _ _ _ n h_inj (algebraPB (triple B B C n h_inj))
      (@Algebra.TensorProduct.rightAlgebra (triple B B C n h_inj).P
        (triple B B C n h_inj).Q B _ _ _ _ (algebraPB (triple B B C n h_inj)))
      (algebraPB (triple A B C n h_inj)))
where
  /-- Instance-resolved construction of `barQToBarRAlg`. -/
  go (n : SimplexCategoryᵒᵖ) (h_inj : Function.Injective (algebraMap B C))
      [Algebra (triple A B C n h_inj).P B] [Algebra (triple B B C n h_inj).P B]
      [Algebra (triple B B C n h_inj).P (triple B B C n h_inj).Q]
      [Algebra B ((triple A B C n h_inj).Q ⊗[(triple A B C n h_inj).P] B)]
      [Algebra B ((triple B B C n h_inj).Q ⊗[(triple B B C n h_inj).P] B)]
      [Algebra (triple A B C n h_inj).P
        ((triple B B C n h_inj).Q ⊗[(triple B B C n h_inj).P] B)] :
      ((triple A B C n h_inj).Q ⊗[(triple A B C n h_inj).P] B) →ₐ[B]
        ((triple B B C n h_inj).Q ⊗[(triple B B C n h_inj).P] B) :=
    { (Algebra.TensorProduct.productMap
          ({ ((Algebra.TensorProduct.includeLeftRingHom
                : (triple B B C n h_inj).Q →+*
                    ((triple B B C n h_inj).Q ⊗[(triple B B C n h_inj).P] B)).comp
              (functorialityQRHom A B C n)) with
            commutes' := sorry }
            : (triple A B C n h_inj).Q →ₐ[(triple A B C n h_inj).P]
                ((triple B B C n h_inj).Q ⊗[(triple B B C n h_inj).P] B))
          ({ (Algebra.TensorProduct.includeRight
                : B →ₐ[(triple B B C n h_inj).P]
                    ((triple B B C n h_inj).Q ⊗[(triple B B C n h_inj).P] B)).toRingHom with
            commutes' := sorry }
            : B →ₐ[(triple A B C n h_inj).P]
                ((triple B B C n h_inj).Q ⊗[(triple B B C n h_inj).P] B))).toRingHom with
      commutes' := sorry }

/-- The over-`C` triangle of `barQToBarRAlg`. -/
theorem barQToBarROver_w (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    CommAlgCat.ofHom (barQToBarRAlg A B C n h_inj) ≫ (barROver B C n h_inj).obj.hom =
      (barQOver A B C n h_inj).obj.hom :=
  sorry

/-- The morphism of polynomial `B`-algebras over `C` from `Q̄_n` to `R̄_n`. -/
def barQToBarROver (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    barQOver A B C n h_inj ⟶ barROver B C n h_inj :=
  ObjectProperty.homMk
    (Over.homMk (CommAlgCat.ofHom (barQToBarRAlg A B C n h_inj))
      (barQToBarROver_w A B C n h_inj))

/-- The underlying `B`-algebra map of `barQToBarROver` is `barQToBarRAlg`. -/
theorem barQToBarROver_app (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    (barQToBarROver A B C n h_inj).hom.left =
      CommAlgCat.ofHom (barQToBarRAlg A B C n h_inj) :=
  sorry

/-- The canonical simplicial `B`-algebra map `Q̄_• ⟶ R̄_•`. -/
def barQToBarR (h_inj : Function.Injective (algebraMap B C)) :
    barQSimplicial A B C h_inj ⟶ barRSimplicial B C h_inj where
  app n := (barQToBarROver A B C n h_inj).hom.left
  naturality _ _ _ := sorry

/-- Components of `barQToBarR` are the left morphisms of `barQToBarROver`. -/
theorem barQToBarR_app (h_inj : Function.Injective (algebraMap B C))
    (n : SimplexCategoryᵒᵖ) :
    (barQToBarR A B C h_inj).app n = (barQToBarROver A B C n h_inj).hom.left :=
  sorry

/-- The polynomial `B`-algebra arrow `R_n ⟶ C` of the standard resolution. -/
abbrev standardROver (n : SimplexCategoryᵒᵖ) : PolynomialOver B C :=
  (asPolynomialSimplicial (standardHom B C) (standard_isPolynomial B C)).obj n

/-- The standard-resolution term of `C` over `B`, as the right object of the under-category
resolution, is a `B`-algebra. -/
@[reducible] instance algebraB_standardTerm (n : SimplexCategoryᵒᵖ) :
    Algebra B (standardTerm (CommRingCat.of B) ((CommRingCat.of B).mkUnder C) n).right :=
  RingHom.toAlgebra
    (standardTerm (CommRingCat.of B) ((CommRingCat.of B).mkUnder C) n).hom.hom

/-- The evaluated standard-resolution term of `C` over `B` is a `B`-algebra. -/
@[reducible] instance algebraB_evalRight (n : SimplexCategoryᵒᵖ) :
    Algebra B
      ((Augmented.drop.obj
          ((evaluation (CommRingCat.of B)).obj
            ((CommRingCat.of B).mkUnder C))).obj n).right :=
  RingHom.toAlgebra
    ((Augmented.drop.obj
        ((evaluation (CommRingCat.of B)).obj
          ((CommRingCat.of B).mkUnder C))).obj n).hom.hom

/-- The standard-resolution term `R_n` of `C` over `B` is a `B`-algebra. -/
@[reducible] instance algebraBStandardR (n : SimplexCategoryᵒᵖ) :
    Algebra B (standardR B C n) :=
  algebraB_standardTerm B C n

/-- The triple source `R_n` is a `B`-algebra. -/
@[reducible] instance algebraB_tripleQ (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    Algebra B (triple B B C n h_inj).Q :=
  algebraB_standardTerm B C n

/-- The `P_n`-algebra structure on `B` associated to a functorial triple. -/
@[reducible] instance instAlgebraPB_triple (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    Algebra (triple B B C n h_inj).P B :=
  algebraPB (triple B B C n h_inj)

/-- The `B`-algebra map `R_n ⟶ R_n ⊗[S_n] B` given by `includeLeft`. -/
def standardToBarRAlg (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :=
  @go n h_inj (algebraB_standardTerm B C n)
    (algebraPB (triple B B C n h_inj)) (triple B B C n h_inj).algebraPQ
    (@Algebra.TensorProduct.rightAlgebra (triple B B C n h_inj).P
      (triple B B C n h_inj).Q B _ _ _ _ (algebraPB (triple B B C n h_inj)))
where
  /-- Instance-resolved construction of `standardToBarRAlg`. -/
  go (n : SimplexCategoryᵒᵖ) (h_inj : Function.Injective (algebraMap B C))
      [Algebra B (triple B B C n h_inj).Q]
      [Algebra (triple B B C n h_inj).P B]
      [Algebra (triple B B C n h_inj).P (triple B B C n h_inj).Q]
      [Algebra B ((triple B B C n h_inj).Q ⊗[(triple B B C n h_inj).P] B)] :
      (triple B B C n h_inj).Q →ₐ[B]
        ((triple B B C n h_inj).Q ⊗[(triple B B C n h_inj).P] B) :=
    { (Algebra.TensorProduct.includeLeftRingHom
          : (triple B B C n h_inj).Q →+*
            ((triple B B C n h_inj).Q ⊗[(triple B B C n h_inj).P] B)) with
      commutes' := sorry }

/-- The morphism of `B`-algebras `R_n ⟶ R̄_n` as a morphism in `CommAlgCat B`. -/
def standardToBarRLeft (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :=
  @go n h_inj (algebraB_tripleQ B C n h_inj)
    (instAlgebraPB_triple B C n h_inj)
    (@Algebra.TensorProduct.rightAlgebra (triple B B C n h_inj).P
      (triple B B C n h_inj).Q B _ _ _ _ (algebraPB (triple B B C n h_inj)))
where
  /-- Instance-resolved morphism of `B`-algebras `R_n ⟶ R̄_n`. -/
  go (n : SimplexCategoryᵒᵖ) (h_inj : Function.Injective (algebraMap B C))
      [Algebra B (triple B B C n h_inj).Q]
      [Algebra (triple B B C n h_inj).P B]
      [Algebra B ((triple B B C n h_inj).Q ⊗[(triple B B C n h_inj).P] B)] :
      (standardROver B C n).obj.left ⟶ (barROver B C n h_inj).obj.left :=
    CommAlgCat.ofHom (standardToBarRAlg B C n h_inj)

/-- The over-`C` triangle of `standardToBarRLeft`. -/
theorem standardToBarROver_w (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    standardToBarRLeft B C n h_inj ≫ (barROver B C n h_inj).obj.hom =
      (standardROver B C n).obj.hom :=
  sorry

/-- The morphism of polynomial `B`-algebras over `C` from `R_n` to `R̄_n`. -/
def standardToBarROver (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    standardROver B C n ⟶ barROver B C n h_inj :=
  ObjectProperty.homMk
    (Over.homMk (CommAlgCat.ofHom (standardToBarRAlg B C n h_inj))
      (standardToBarROver_w B C n h_inj))

/-- The underlying `B`-algebra map of `standardToBarROver` is `includeLeft`. -/
theorem standardToBarROver_app (n : SimplexCategoryᵒᵖ)
    (h_inj : Function.Injective (algebraMap B C)) :
    (standardToBarROver B C n h_inj).hom.left =
      standardToBarRLeft B C n h_inj :=
  sorry

/-- The simplicial `B`-algebra map `R_• ⟶ R̄_•`. -/
def standardToBarR (h_inj : Function.Injective (algebraMap B C)) :
    (standardAugmented B C).left ⟶ barRSimplicial B C h_inj where
  app n := (standardToBarROver B C n h_inj).hom.left
  naturality _ _ _ := sorry

/-- Components of `standardToBarR` are the left morphisms of `standardToBarROver`. -/
theorem standardToBarR_app (h_inj : Function.Injective (algebraMap B C))
    (n : SimplexCategoryᵒᵖ) :
    (standardToBarR B C h_inj).app n = (standardToBarROver B C n h_inj).hom.left :=
  sorry

/-- The simplicial `C`-module `Ω_{R̄_•/B} ⊗_{R̄_•} C`. -/
abbrev omegaBarRSimplicial (h_inj : Function.Injective (algebraMap B C)) :
    SimplicialObject (ModuleCat.{u} C) :=
  omegaBarQSimplicial B B C h_inj

/-- The cochain complex of `C`-modules associated to `Ω_{R̄_•/B} ⊗_{R̄_•} C`. -/
abbrev omegaBarRCochain (h_inj : Function.Injective (algebraMap B C)) :
    CochainComplex (ModuleCat.{u} C) ℤ :=
  omegaBarQCochain B B C h_inj

/-- The simplicial map on naive differentials induced by `Q̄_• ⟶ R̄_•`. -/
def omegaBarQToBarRSimplicial (h_inj : Function.Injective (algebraMap B C)) :
    omegaBarQSimplicial A B C h_inj ⟶ omegaBarRSimplicial B C h_inj where
  app n := omegaSheafMap (barQToBarROver A B C n h_inj)
  naturality _ _ _ := sorry

/-- Components of `omegaBarQToBarRSimplicial` are `omegaSheafMap` of `barQToBarROver`. -/
theorem omegaBarQToBarRSimplicial_app (h_inj : Function.Injective (algebraMap B C))
    (n : SimplexCategoryᵒᵖ) :
    (omegaBarQToBarRSimplicial A B C h_inj).app n =
      omegaSheafMap (barQToBarROver A B C n h_inj) :=
  sorry

/-- The cochain map `Ω_{Q̄_•/B} ⊗ C ⟶ Ω_{R̄_•/B} ⊗ C` induced by `Q̄_• ⟶ R̄_•`. -/
def omegaBarQToBarR (h_inj : Function.Injective (algebraMap B C)) :
    omegaBarQCochain A B C h_inj ⟶ omegaBarRCochain B C h_inj :=
  (simplicialModuleToCochain C).map (omegaBarQToBarRSimplicial A B C h_inj)

/-- Unfolding `omegaBarQToBarR` recovers the extended alternating-face image of
`omegaBarQToBarRSimplicial`. -/
theorem omegaBarQToBarR_eq (h_inj : Function.Injective (algebraMap B C)) :
    omegaBarQToBarR A B C h_inj =
      (simplicialModuleToCochain C).map (omegaBarQToBarRSimplicial A B C h_inj) :=
  sorry

/-- `omegaBarQToBarR` is a quasi-isomorphism. -/
instance omegaBarQToBarR_quasiIso (h_inj : Function.Injective (algebraMap B C)) :
    QuasiIso (omegaBarQToBarR A B C h_inj) :=
  sorry

/-- Naive differentials `Ω_{R_•/B} ⊗_{R_•} C` of the standard resolution of `C` over `B`,
as a simplicial `C`-module. -/
abbrev omegaEvalSimplicial : SimplicialObject (ModuleCat.{u} C) :=
  asPolynomialSimplicial (standardHom B C) (standard_isPolynomial B C) ⋙ omegaSheafCov B C

/-- Degreewise, `omegaEvalSimplicial` is naive differentials of `standardROver`. -/
theorem omegaEvalSimplicial_obj (n : SimplexCategoryᵒᵖ) :
    (omegaEvalSimplicial B C).obj n = omegaSheafObj (standardROver B C n) :=
  sorry

/-- The cochain complex `Ω_{R_•/B} ⊗_{R_•} C` of naive differentials of the standard
resolution of `C` over `B`. -/
abbrev omegaEvalCochain : CochainComplex (ModuleCat.{u} C) ℤ :=
  (simplicialModuleToCochain C).obj (omegaEvalSimplicial B C)

/-- The simplicial map on naive differentials induced by `R_• ⟶ R̄_•`. -/
def omegaEvalToBarRSimplicial (h_inj : Function.Injective (algebraMap B C)) :
    omegaEvalSimplicial B C ⟶ omegaBarRSimplicial B C h_inj where
  app n := omegaSheafMap (standardToBarROver B C n h_inj)
  naturality _ _ _ := sorry

/-- Components of `omegaEvalToBarRSimplicial` are `omegaSheafMap` of `standardToBarROver`. -/
theorem omegaEvalToBarRSimplicial_app (h_inj : Function.Injective (algebraMap B C))
    (n : SimplexCategoryᵒᵖ) :
    (omegaEvalToBarRSimplicial B C h_inj).app n =
      omegaSheafMap (standardToBarROver B C n h_inj) :=
  sorry

/-- The cochain map `Ω_{R_•/B} ⊗ C ⟶ Ω_{R̄_•/B} ⊗ C` induced by `R_• ⟶ R̄_•`. -/
def omegaEvalToBarR (h_inj : Function.Injective (algebraMap B C)) :
    omegaEvalCochain B C ⟶ omegaBarRCochain B C h_inj :=
  (simplicialModuleToCochain C).map (omegaEvalToBarRSimplicial B C h_inj)

/-- Unfolding `omegaEvalToBarR` recovers the extended alternating-face image of
`omegaEvalToBarRSimplicial`. -/
theorem omegaEvalToBarR_eq (h_inj : Function.Injective (algebraMap B C)) :
    omegaEvalToBarR B C h_inj =
      (simplicialModuleToCochain C).map (omegaEvalToBarRSimplicial B C h_inj) :=
  sorry

/-- `omegaEvalToBarR` is a quasi-isomorphism. -/
instance omegaEvalToBarR_quasiIso (h_inj : Function.Injective (algebraMap B C)) :
    QuasiIso (omegaEvalToBarR B C h_inj) :=
  sorry

/-- Composing `omegaBarQToBarR` with the inverse of `omegaEvalToBarR` identifies
`Ω_{Q̄_•/B} ⊗_{Q̄_•} C` with `Ω_{R_•/B} ⊗_{R_•} C` in `D(C)`. -/
theorem barQ_iso_omegaEval (h_inj : Function.Injective (algebraMap B C))
    [HasDerivedCategory.{q} (ModuleCat.{u} C)] :
    IsIso (DerivedCategory.Q.map (omegaBarQToBarR A B C h_inj) ≫
      inv (DerivedCategory.Q.map (omegaEvalToBarR B C h_inj))) :=
  sorry

/-- `omegaBarQToBarR` is an isomorphism in `D(C)`. -/
theorem barQ_iso_cotangent_map_barQ (h_inj : Function.Injective (algebraMap B C))
    [HasDerivedCategory.{q} (ModuleCat.{u} C)] :
    IsIso (DerivedCategory.Q.map (omegaBarQToBarR A B C h_inj)) :=
  sorry

/-- `omegaEvalToBarR` is an isomorphism in `D(C)`. -/
theorem barQ_iso_cotangent_map_eval (h_inj : Function.Injective (algebraMap B C))
    [HasDerivedCategory.{q} (ModuleCat.{u} C)] :
    IsIso (DerivedCategory.Q.map (omegaEvalToBarR B C h_inj)) :=
  sorry

end Algebra.CotangentComplex
