module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Single
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived
public import stacks_project.Chap92.Lemma_92_3_4_DirectLimit
public import stacks_project.Chap92.Lemma_92_24_3_Comparison
public import stacks_project.Chap92.Lemma_92_25_3_Omega
public import stacks_project.Chap92.Remark_92_18_5_Sections
public import stacks_project.Chap92.Remark_92_25_2_Cosimplicial

/-!
# Evaluation of `i^* Ω` on standard fibrewise affine spaces

This leaf owns the explicit complex `Lπ_!(Ω_{O / underline{Λ}} ⊗_O underline{O}_X)`
on a `Λ`-scheme `X`, obtained by sheafifying `U ↦ (i^* Ω)(A_{n,U})`, and the
canonical identification of `L_{X / Spec Λ}` with that complex in `D(O_X)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicTopology
open HomologicalComplex
open ComplexShape
open SheafOfModules.RingedSite
open TopologicalSpace
open scoped AlgebraicGeometry Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CotangentSite

variable (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)]

/-- The value of `i^* Ω` on the standard affine space `A_{n,U}`. -/
def omegaEvalSiteObj (n : ℕ) (U : X.smallZariskiSite) :
    ModuleCat.{u} (sectionsRing Λ X U) :=
  omegaPullbackObj Λ X (standardAffine Λ X ⦋n⦌ U)

/-- Unfolding of `omegaEvalSiteObj` as `omegaPullback` on `standardAffine`. -/
theorem omegaEvalSiteObj_eq (n : ℕ) (U : X.smallZariskiSite) :
    omegaEvalSiteObj Λ X n U =
      omegaPullbackObj Λ X (standardAffine Λ X ⦋n⦌ U) :=
  sorry

/-- Restriction of `omegaEvalSiteObj` along a morphism of the small Zariski site. -/
def omegaEvalSiteMap (n : ℕ) {V U : X.smallZariskiSite} (f : V ⟶ U) :
    omegaEvalSiteObj Λ X n U ⟶
      (ModuleCat.restrictScalars (sectionsRestrict Λ X f).hom).obj
        (omegaEvalSiteObj Λ X n V) :=
  omegaPullbackMap Λ X (standardAffineRestrict Λ X f ⦋n⦌).op

/-- Unfolding of `omegaEvalSiteMap` as `omegaPullbackMap` of `standardAffineRestrict`. -/
theorem omegaEvalSiteMap_eq (n : ℕ) {V U : X.smallZariskiSite} (f : V ⟶ U) :
    omegaEvalSiteMap Λ X n f =
      omegaPullbackMap Λ X (standardAffineRestrict Λ X f ⦋n⦌).op :=
  sorry

/-- Simplicial operators of `A_{•,U}` act on `omegaEvalSiteObj`. -/
def omegaEvalSiteSimplicialMap {n m : SimplexCategory} (f : n ⟶ m)
    (U : X.smallZariskiSite) :
    omegaEvalSiteObj Λ X m.len U ⟶
      (ModuleCat.restrictScalars
        ((inverseImageStructureSheafComm Λ X).obj.map
          (standardAffineHom Λ X f U).op).hom).obj
        (omegaEvalSiteObj Λ X n.len U) :=
  omegaPullbackMap Λ X (standardAffineHom Λ X f U).op

/-- Unfolding of `omegaEvalSiteSimplicialMap`. -/
theorem omegaEvalSiteSimplicialMap_eq {n m : SimplexCategory} (f : n ⟶ m)
    (U : X.smallZariskiSite) :
    omegaEvalSiteSimplicialMap Λ X f U =
      omegaPullbackMap Λ X (standardAffineHom Λ X f U).op :=
  sorry

/-- Transport of `omegaEvalSiteObj` from the small Zariski site to an open of `X`. -/
def omegaEvalPresheafObj (n : ℕ) (U : X.Opensᵒᵖ) :
    ModuleCat.{u} (X.ringCatSheaf.obj.obj U) :=
  (ModuleCat.extendScalars ((X.restrictFunctorΓ).hom.app U).hom).obj
    (omegaEvalSiteObj Λ X n ((smallZariskiOpenFunctor X).obj U.unop))

/-- Unfolding of `omegaEvalPresheafObj` as extension of scalars of `omegaEvalSiteObj`. -/
theorem omegaEvalPresheafObj_eq (n : ℕ) (U : X.Opensᵒᵖ) :
    omegaEvalPresheafObj Λ X n U =
      (ModuleCat.extendScalars ((X.restrictFunctorΓ).hom.app U).hom).obj
        (omegaEvalSiteObj Λ X n ((smallZariskiOpenFunctor X).obj U.unop)) :=
  sorry

/-- The composite restriction `O_X(U) ⟶ O_X(V)` via the small Zariski site agrees with
the structure-sheaf restriction of `X`. -/
theorem omegaEvalPresheafMap_comp_eq {U V : X.Opensᵒᵖ} (f : U ⟶ V) :
    ((X.restrictFunctorΓ).hom.app V).hom.comp
        (sectionsRestrict Λ X ((smallZariskiOpenFunctor X).map f.unop)).hom =
      (X.ringCatSheaf.obj.map f).hom.comp ((X.restrictFunctorΓ).hom.app U).hom :=
  sorry

/-- Restriction of `omegaEvalPresheafObj` along an inclusion of opens. -/
def omegaEvalPresheafMap (n : ℕ) {U V : X.Opensᵒᵖ} (f : U ⟶ V) :
    omegaEvalPresheafObj Λ X n U ⟶
      (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map f).hom).obj
        (omegaEvalPresheafObj Λ X n V) :=
  ((ModuleCat.extendRestrictScalarsAdj ((X.restrictFunctorΓ).hom.app U).hom).homEquiv _ _).symm
    ((omegaEvalSiteMap Λ X n ((smallZariskiOpenFunctor X).map f.unop)) ≫
      (ModuleCat.restrictScalars (sectionsRestrict Λ X
          ((smallZariskiOpenFunctor X).map f.unop)).hom).map
        ((ModuleCat.extendRestrictScalarsAdj
            ((X.restrictFunctorΓ).hom.app V).hom).unit.app
          (omegaEvalSiteObj Λ X n ((smallZariskiOpenFunctor X).obj V.unop))) ≫
      (ModuleCat.restrictScalarsComp'
          (sectionsRestrict Λ X ((smallZariskiOpenFunctor X).map f.unop)).hom
          ((X.restrictFunctorΓ).hom.app V).hom
          (((X.restrictFunctorΓ).hom.app V).hom.comp
            (sectionsRestrict Λ X ((smallZariskiOpenFunctor X).map f.unop)).hom)
          rfl).inv.app _ ≫
      (ModuleCat.restrictScalarsCongr (omegaEvalPresheafMap_comp_eq Λ X f)).hom.app _ ≫
      (ModuleCat.restrictScalarsComp'
          ((X.restrictFunctorΓ).hom.app U).hom (X.ringCatSheaf.obj.map f).hom
          ((X.ringCatSheaf.obj.map f).hom.comp ((X.restrictFunctorΓ).hom.app U).hom)
          rfl).hom.app _)

/-- Unfolding of `omegaEvalPresheafMap`. -/
theorem omegaEvalPresheafMap_eq (n : ℕ) {U V : X.Opensᵒᵖ} (f : U ⟶ V) :
    omegaEvalPresheafMap Λ X n f =
      ((ModuleCat.extendRestrictScalarsAdj ((X.restrictFunctorΓ).hom.app U).hom).homEquiv
          _ _).symm
        ((omegaEvalSiteMap Λ X n ((smallZariskiOpenFunctor X).map f.unop)) ≫
          (ModuleCat.restrictScalars (sectionsRestrict Λ X
              ((smallZariskiOpenFunctor X).map f.unop)).hom).map
            ((ModuleCat.extendRestrictScalarsAdj
                ((X.restrictFunctorΓ).hom.app V).hom).unit.app
              (omegaEvalSiteObj Λ X n ((smallZariskiOpenFunctor X).obj V.unop))) ≫
          (ModuleCat.restrictScalarsComp'
              (sectionsRestrict Λ X ((smallZariskiOpenFunctor X).map f.unop)).hom
              ((X.restrictFunctorΓ).hom.app V).hom
              (((X.restrictFunctorΓ).hom.app V).hom.comp
                (sectionsRestrict Λ X ((smallZariskiOpenFunctor X).map f.unop)).hom)
              rfl).inv.app _ ≫
          (ModuleCat.restrictScalarsCongr (omegaEvalPresheafMap_comp_eq Λ X f)).hom.app _ ≫
          (ModuleCat.restrictScalarsComp'
              ((X.restrictFunctorΓ).hom.app U).hom (X.ringCatSheaf.obj.map f).hom
              ((X.ringCatSheaf.obj.map f).hom.comp ((X.restrictFunctorΓ).hom.app U).hom)
              rfl).hom.app _) :=
  sorry

/-- The presheaf of `O_X`-modules `U ↦ (i^* Ω)(A_{n,U})`. -/
def omegaEvalPresheaf (n : ℕ) : _root_.PresheafOfModules.{u} (X.ringCatSheaf.obj) where
  obj U := omegaEvalPresheafObj Λ X n U
  map f := omegaEvalPresheafMap Λ X n f
  map_id := sorry
  map_comp := sorry

/-- Evaluating `omegaEvalPresheaf` at an open recovers `omegaEvalPresheafObj`. -/
theorem omegaEvalPresheaf_obj (n : ℕ) (U : X.Opens) :
    (omegaEvalPresheaf Λ X n).obj (op U) = omegaEvalPresheafObj Λ X n (op U) :=
  sorry

/-- Sheafification of `U ↦ (i^* Ω)(A_{n,U})` as an object of `X.Modules`. -/
def omegaEvalSheaf (n : ℕ) : X.Modules :=
  (RingedSpace.moduleSheafification X.toRingedSpace).obj (omegaEvalPresheaf Λ X n)

/-- Unfolding of `omegaEvalSheaf` as module sheafification of `omegaEvalPresheaf`. -/
theorem omegaEvalSheaf_eq (n : ℕ) :
    omegaEvalSheaf Λ X n =
      (RingedSpace.moduleSheafification X.toRingedSpace).obj
        (omegaEvalPresheaf Λ X n) :=
  sorry

/-- Simplicial operators of `A_{•,U}` act as the identity on `O_X(U)`. -/
theorem omegaEvalPresheafSimplicial_restrict_eq {n m : SimplexCategory} (f : n ⟶ m)
    (U : X.smallZariskiSite) :
    ((inverseImageStructureSheafComm Λ X).obj.map (standardAffineHom Λ X f U).op).hom =
      RingHom.id (sectionsRing Λ X U) :=
  sorry

/-- Simplicial operators act on `omegaEvalPresheaf`. -/
def omegaEvalPresheafSimplicialMap {n m : SimplexCategory} (f : n ⟶ m) :
    omegaEvalPresheaf Λ X m.len ⟶ omegaEvalPresheaf Λ X n.len where
  app U :=
    (ModuleCat.extendScalars ((X.restrictFunctorΓ).hom.app U).hom).map
        (omegaEvalSiteSimplicialMap Λ X f ((smallZariskiOpenFunctor X).obj U.unop) ≫
          (ModuleCat.restrictScalarsId'
              ((inverseImageStructureSheafComm Λ X).obj.map
                  (standardAffineHom Λ X f
                    ((smallZariskiOpenFunctor X).obj U.unop)).op).hom
              (omegaEvalPresheafSimplicial_restrict_eq Λ X f
                ((smallZariskiOpenFunctor X).obj U.unop))).hom.app _)
  naturality := fun {_ _} _ ↦ sorry

/-- Unfolding of `omegaEvalPresheafSimplicialMap` at an open. -/
theorem omegaEvalPresheafSimplicialMap_app {n m : SimplexCategory} (f : n ⟶ m)
    (U : X.Opensᵒᵖ) :
    (omegaEvalPresheafSimplicialMap Λ X f).app U =
      (ModuleCat.extendScalars ((X.restrictFunctorΓ).hom.app U).hom).map
        (omegaEvalSiteSimplicialMap Λ X f ((smallZariskiOpenFunctor X).obj U.unop) ≫
          (ModuleCat.restrictScalarsId'
              ((inverseImageStructureSheafComm Λ X).obj.map
                  (standardAffineHom Λ X f
                    ((smallZariskiOpenFunctor X).obj U.unop)).op).hom
              (omegaEvalPresheafSimplicial_restrict_eq Λ X f
                ((smallZariskiOpenFunctor X).obj U.unop))).hom.app _) :=
  sorry

/-- The simplicial object in `X.Modules` obtained by sheafifying `U ↦ (i^* Ω)(A_{•,U})`. -/
def omegaEvalSimplicial : SimplicialObject X.Modules where
  obj n := omegaEvalSheaf Λ X n.unop.len
  map f := (RingedSpace.moduleSheafification X.toRingedSpace).map
    (omegaEvalPresheafSimplicialMap Λ X f.unop)
  map_id := sorry
  map_comp := sorry

/-- Degree `n` of `omegaEvalSimplicial` is `omegaEvalSheaf n`. -/
theorem omegaEvalSimplicial_obj (n : SimplexCategoryᵒᵖ) :
    (omegaEvalSimplicial Λ X).obj n = omegaEvalSheaf Λ X n.unop.len :=
  sorry

/-- The cochain complex of `O_X`-modules whose term in cohomological degree `-n` is the
sheafification of `U ↦ (i^* Ω)(A_{n,U})`. -/
def omegaEvalSheafComplex : CochainComplex X.Modules ℤ :=
  ((alternatingFaceMapComplex X.Modules).obj (omegaEvalSimplicial Λ X)).extend
    embeddingDownNat

/-- Unfolding of `omegaEvalSheafComplex` as the extended alternating-face complex. -/
theorem omegaEvalSheafComplex_eq :
    omegaEvalSheafComplex Λ X =
      ((alternatingFaceMapComplex X.Modules).obj (omegaEvalSimplicial Λ X)).extend
        embeddingDownNat :=
  sorry

/-- In cohomological degree `-n`, `omegaEvalSheafComplex` is `omegaEvalSheaf n`. -/
theorem omegaEvalSheafComplex_X (n : ℕ) :
    (omegaEvalSheafComplex Λ X).X (-n) = omegaEvalSheaf Λ X n :=
  sorry

/-- The object `Lπ_!(i^* Ω_{O / underline{Λ}})` in `D(O_X)`. -/
def lowerShriekOmega : DerivedCategory X.Modules :=
  DerivedCategory.Q.obj (omegaEvalSheafComplex Λ X)

/-- Unfolding of `lowerShriekOmega`. -/
theorem lowerShriekOmega_eq :
    lowerShriekOmega Λ X = DerivedCategory.Q.obj (omegaEvalSheafComplex Λ X) :=
  sorry

/-- Global sections of `A_{n,U}` map to the polynomial model of `P_{n,U}` by the
Gamma-Spec identification. -/
def omegaEvalToPolynomial (n : ℕ) (U : X.smallZariskiSite) :
    Γ((standardAffine Λ X ⦋n⦌ U).A, ⊤) ⟶ (standardPolynomial Λ X ⦋n⦌ U).right :=
  (Scheme.ΓSpecIso (standardPolynomial Λ X ⦋n⦌ U).right).hom

/-- Unfolding of `omegaEvalToPolynomial` as `ΓSpecIso`. -/
theorem omegaEvalToPolynomial_eq (n : ℕ) (U : X.smallZariskiSite) :
    omegaEvalToPolynomial Λ X n U =
      (Scheme.ΓSpecIso (standardPolynomial Λ X ⦋n⦌ U).right).hom :=
  sorry

/-- The categorical free algebra on `standardVars n U` is the degree-`n` standard-resolution
term of `O_X(U)` over `Λ`. -/
theorem omegaEvalStandardTerm_eq (n : ℕ) (U : X.smallZariskiSite) :
    (CommRingCat.Under.FreeAlgebra.algebraic Λ (standardVars Λ X n U)).right =
      (CommRingCat.Under.CotangentComplex.standardTerm Λ
        (standardAlgebra Λ X U) (op ⦋n⦌)).right :=
  sorry

/-- The polynomial model of `A_{n,U}` maps to the categorical standard-resolution term of
`O_X(U)` over `Λ`. -/
def omegaEvalPolynomialToStandard (n : ℕ) (U : X.smallZariskiSite) :
    (standardPolynomial Λ X ⦋n⦌ U).right ⟶
      (CommRingCat.Under.CotangentComplex.standardTerm Λ
        (standardAlgebra Λ X U) (op ⦋n⦌)).right :=
  (CommRingCat.Under.FreeAlgebra.polynomialIso Λ (standardVars Λ X n U)).inv.right

/-- Composite ring map from global sections of `A_{n,U}` to the standard-resolution term of
`O_X(U)`. -/
def omegaEvalStandardRingHom (n : ℕ) (U : X.smallZariskiSite) :
    Γ((standardAffine Λ X ⦋n⦌ U).A, ⊤) ⟶
      (CommRingCat.Under.CotangentComplex.standardTerm Λ
        (standardAlgebra Λ X U) (op ⦋n⦌)).right :=
  omegaEvalToPolynomial Λ X n U ≫ omegaEvalPolynomialToStandard Λ X n U

/-- Unfolding of `omegaEvalStandardRingHom`. -/
theorem omegaEvalStandardRingHom_eq (n : ℕ) (U : X.smallZariskiSite) :
    omegaEvalStandardRingHom Λ X n U =
      omegaEvalToPolynomial Λ X n U ≫ omegaEvalPolynomialToStandard Λ X n U :=
  sorry

/-- The polynomial identification square for Kähler differentials of `A_{n,U}`. -/
theorem omegaEvalKaehlerSquare (n : ℕ) (U : X.smallZariskiSite) :
    (CommRingCat.Under.CotangentComplex.standardTerm Λ
        (standardAlgebra Λ X U) (op ⦋n⦌)).hom =
      structureMap Λ X (standardAffine Λ X ⦋n⦌ U) ≫
        omegaEvalStandardRingHom Λ X n U :=
  sorry

/-- The augmentations `P_{n,U} ⟶ O_X(U)` are compatible with `omegaEvalStandardRingHom`. -/
theorem omegaEvalAugmentation_comp (n : ℕ) (U : X.smallZariskiSite) :
    (CommRingCat.Under.CotangentComplex.standardAugmentation Λ
          (standardAlgebra Λ X U) (op ⦋n⦌)).hom.comp
        (omegaEvalStandardRingHom Λ X n U).hom =
      (standardAffine Λ X ⦋n⦌ U).hom.appTop.hom :=
  sorry

/-- Fibrewise naive differentials on `A_{n,U}` map to the degree-`n` standard-resolution
term of `L_{O_X(U) / Λ}`. -/
def omegaEvalSiteToSimplicial (n : ℕ) (U : X.smallZariskiSite) :
    omegaEvalSiteObj Λ X n U ⟶
      (CommRingCat.Under.CotangentComplex.simplicialModule Λ
        (standardAlgebra Λ X U)).obj (op ⦋n⦌) :=
  ((ModuleCat.extendRestrictScalarsAdj
      (standardAffine Λ X ⦋n⦌ U).hom.appTop.hom).homEquiv _ _).symm
    (CommRingCat.KaehlerDifferential.map
        ((Category.id_comp
            (CommRingCat.Under.CotangentComplex.standardTerm Λ
              (standardAlgebra Λ X U) (op ⦋n⦌)).hom).trans
          (omegaEvalKaehlerSquare Λ X n U)) ≫
      (ModuleCat.restrictScalars (omegaEvalStandardRingHom Λ X n U).hom).map
        ((ModuleCat.extendRestrictScalarsAdj
            (CommRingCat.Under.CotangentComplex.standardAugmentation Λ
              (standardAlgebra Λ X U) (op ⦋n⦌)).hom).unit.app
          (CommRingCat.KaehlerDifferential
            (CommRingCat.Under.CotangentComplex.standardTerm Λ
              (standardAlgebra Λ X U) (op ⦋n⦌)).hom)) ≫
      (ModuleCat.restrictScalarsComp'
          (omegaEvalStandardRingHom Λ X n U).hom
          (CommRingCat.Under.CotangentComplex.standardAugmentation Λ
            (standardAlgebra Λ X U) (op ⦋n⦌)).hom
          (standardAffine Λ X ⦋n⦌ U).hom.appTop.hom
          (omegaEvalAugmentation_comp Λ X n U).symm).inv.app _)

/-- Unfolding of `omegaEvalSiteToSimplicial` as the adjunct of the polynomial Kähler
comparison. -/
theorem omegaEvalSiteToSimplicial_eq (n : ℕ) (U : X.smallZariskiSite) :
    omegaEvalSiteToSimplicial Λ X n U =
      ((ModuleCat.extendRestrictScalarsAdj
          (standardAffine Λ X ⦋n⦌ U).hom.appTop.hom).homEquiv _ _).symm
        (CommRingCat.KaehlerDifferential.map
        ((Category.id_comp
            (CommRingCat.Under.CotangentComplex.standardTerm Λ
              (standardAlgebra Λ X U) (op ⦋n⦌)).hom).trans
          (omegaEvalKaehlerSquare Λ X n U)) ≫
          (ModuleCat.restrictScalars (omegaEvalStandardRingHom Λ X n U).hom).map
            ((ModuleCat.extendRestrictScalarsAdj
                (CommRingCat.Under.CotangentComplex.standardAugmentation Λ
                  (standardAlgebra Λ X U) (op ⦋n⦌)).hom).unit.app
              (CommRingCat.KaehlerDifferential
                (CommRingCat.Under.CotangentComplex.standardTerm Λ
                  (standardAlgebra Λ X U) (op ⦋n⦌)).hom)) ≫
          (ModuleCat.restrictScalarsComp'
              (omegaEvalStandardRingHom Λ X n U).hom
              (CommRingCat.Under.CotangentComplex.standardAugmentation Λ
                (standardAlgebra Λ X U) (op ⦋n⦌)).hom
              (standardAffine Λ X ⦋n⦌ U).hom.appTop.hom
              (omegaEvalAugmentation_comp Λ X n U).symm).inv.app _) :=
  sorry

/-- The sheafification-unit component `Λ ⟶ underline{Λ}(U)` on the Zariski site of `X`. -/
def constRingSheafUnitApp (U : X.Opensᵒᵖ) :
    Λ ⟶ (Cotangent.constRingSheaf Λ X).obj.obj U :=
  ((sheafificationAdjunction (Opens.grothendieckTopology X.toTopCat) CommRingCat.{u}).unit.app
      ((Functor.const (TopologicalSpace.Opens X.toTopCat)ᵒᵖ).obj Λ)).app U

/-- Unfolding of `constRingSheafUnitApp` as the sheafification-unit component. -/
theorem constRingSheafUnitApp_eq (U : X.Opensᵒᵖ) :
    constRingSheafUnitApp Λ X U =
      ((sheafificationAdjunction (Opens.grothendieckTopology X.toTopCat) CommRingCat.{u}).unit.app
          ((Functor.const (TopologicalSpace.Opens X.toTopCat)ᵒᵖ).obj Λ)).app U :=
  sorry

/-- `Scheme.restrictFunctorΓ` identifies the structure map `Λ ⟶ Γ(U, ⊤)` with the component
of `constToStructure` after the sheafification unit. -/
theorem sectionsHom_restrictFunctorΓ (U : X.Opensᵒᵖ) :
    ((Cotangent.constToStructure Λ X).hom.app U).hom.comp
        (constRingSheafUnitApp Λ X U).hom =
      ((X.restrictFunctorΓ).hom.app U).hom.comp
        (sectionsHom Λ X ((smallZariskiOpenFunctor X).obj U.unop)).hom :=
  sorry

/-- The cochain map induced by `restrictFunctorΓ` and the sheafification unit
`constRingSheafUnitApp` from `L_{Γ(U, ⊤) / Λ}` to `L_{O_X(U) / underline{Λ}(U)}`
after restriction of scalars. This is not a degreewise isomorphism: the unit
`Λ ⟶ underline{Λ}(U)` need not be an isomorphism. -/
def sectionsHomCotangentToConst (U : X.Opensᵒᵖ) :
    RingHom.cotangentComplex
        (sectionsHom Λ X ((smallZariskiOpenFunctor X).obj U.unop)).hom ⟶
      ((ModuleCat.restrictScalars ((X.restrictFunctorΓ).hom.app U).hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (RingHom.cotangentComplex ((Cotangent.constToStructure Λ X).hom.app U).hom) where
  f i :=
    ((ModuleCat.extendRestrictScalarsAdj ((X.restrictFunctorΓ).hom.app U).hom).homEquiv _ _)
      ((Algebra.CotangentComplex.map
          (sectionsHom Λ X ((smallZariskiOpenFunctor X).obj U.unop)).hom
          ((Cotangent.constToStructure Λ X).hom.app U).hom
          (constRingSheafUnitApp Λ X U).hom
          ((X.restrictFunctorΓ).hom.app U).hom
          (sectionsHom_restrictFunctorΓ Λ X U)).f i)
  comm' := sorry

/-- Degreewise, `sectionsHomCotangentToConst` is the adjunct of `Algebra.CotangentComplex.map`. -/
theorem sectionsHomCotangentToConst_f (U : X.Opensᵒᵖ) (i : ℤ) :
    (sectionsHomCotangentToConst Λ X U).f i =
      ((ModuleCat.extendRestrictScalarsAdj ((X.restrictFunctorΓ).hom.app U).hom).homEquiv
          _ _)
        ((Algebra.CotangentComplex.map
            (sectionsHom Λ X ((smallZariskiOpenFunctor X).obj U.unop)).hom
            ((Cotangent.constToStructure Λ X).hom.app U).hom
            (constRingSheafUnitApp Λ X U).hom
            ((X.restrictFunctorΓ).hom.app U).hom
            (sectionsHom_restrictFunctorΓ Λ X U)).f i) :=
  sorry

/-- Degreewise polynomial comparison from fibrewise `Ω_{P_{n,U}/Λ} ⊗ O_X(U)` to the
standard-resolution term of `L_{O_X(U) / underline{Λ}(U)}`. -/
def omegaEvalToRingCotangent (n : ℕ) (U : X.Opensᵒᵖ) :
    omegaEvalPresheafObj Λ X n U ⟶
      (RingHom.cotangentComplex
        ((Cotangent.constToStructure Λ X).hom.app U).hom).X (-n) :=
  ((ModuleCat.extendRestrictScalarsAdj ((X.restrictFunctorΓ).hom.app U).hom).homEquiv _ _).symm
    (omegaEvalSiteToSimplicial Λ X n ((smallZariskiOpenFunctor X).obj U.unop) ≫
      (CommRingCat.Under.CotangentComplex.objXIso Λ
          (standardAlgebra Λ X ((smallZariskiOpenFunctor X).obj U.unop)) n).inv ≫
        (sectionsHomCotangentToConst Λ X U).f (-n))

/-- Unfolding of `omegaEvalToRingCotangent` through the polynomial comparison,
`objXIso`, and `sectionsHomCotangentToConst`. -/
theorem omegaEvalToRingCotangent_eq (n : ℕ) (U : X.Opensᵒᵖ) :
    omegaEvalToRingCotangent Λ X n U =
      ((ModuleCat.extendRestrictScalarsAdj ((X.restrictFunctorΓ).hom.app U).hom).homEquiv
          _ _).symm
        (omegaEvalSiteToSimplicial Λ X n ((smallZariskiOpenFunctor X).obj U.unop) ≫
          (CommRingCat.Under.CotangentComplex.objXIso Λ
              (standardAlgebra Λ X ((smallZariskiOpenFunctor X).obj U.unop)) n).inv ≫
            (sectionsHomCotangentToConst Λ X U).f (-n)) :=
  sorry

/-- Presheaf-level comparison from `U ↦ (i^* Ω)(A_{n,U})` to the underlying presheaf of
`L_{O_X / underline{Λ}}` in cohomological degree `-n`. -/
def omegaEvalToConstPresheaf (n : ℕ) :
    omegaEvalPresheaf Λ X n ⟶
      (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
        ((SheafOfModules.forget X.ringCatSheaf).obj
          ((Cotangent.constCotangentCochain Λ X).X (-n))) where
  app U :=
    omegaEvalToRingCotangent Λ X n U ≫
      (SheafOfModules.RingedSite.CotangentComplex.Homology.sectionsComplexMap
          (Cotangent.constToStructure Λ X) U).f (-n)
  naturality := fun {_ _} _ ↦ sorry

/-- Unfolding of `omegaEvalToConstPresheaf` at an open. -/
theorem omegaEvalToConstPresheaf_app (n : ℕ) (U : X.Opensᵒᵖ) :
    (omegaEvalToConstPresheaf Λ X n).app U =
      omegaEvalToRingCotangent Λ X n U ≫
        (SheafOfModules.RingedSite.CotangentComplex.Homology.sectionsComplexMap
            (Cotangent.constToStructure Λ X) U).f (-n) :=
  sorry

/-- The cohomological degree `-n` term of `omegaEvalSheafComplex` is `omegaEvalSheaf n`. -/
def omegaEvalSheafComplexXIso (n : ℕ) :
    (omegaEvalSheafComplex Λ X).X (-n) ≅ omegaEvalSheaf Λ X n :=
  extendXIso
    ((alternatingFaceMapComplex X.Modules).obj (omegaEvalSimplicial Λ X))
    embeddingDownNat
    (rfl : embeddingDownNat.f n = -n)

/-- Unfolding of `omegaEvalSheafComplexXIso`. -/
theorem omegaEvalSheafComplexXIso_eq (n : ℕ) :
    omegaEvalSheafComplexXIso Λ X n =
      extendXIso
        ((alternatingFaceMapComplex X.Modules).obj (omegaEvalSimplicial Λ X))
        embeddingDownNat
        (rfl : embeddingDownNat.f n = -n) :=
  sorry

/-- Degreewise comparison from the explicit `Lπ_!` complex to `L_{O_X / underline{Λ}}`.
Components are the sheafification adjunct of the polynomial comparison composed with
`Homology.sectionsComplexMap`. -/
def omegaEvalToConstCotangent :
    omegaEvalSheafComplex Λ X ⟶ Cotangent.constCotangentCochain Λ X where
  f i :=
    match h : embeddingDownNat.r i with
    | some n =>
        (extendXIso
            ((alternatingFaceMapComplex X.Modules).obj (omegaEvalSimplicial Λ X))
            embeddingDownNat (embeddingDownNat.f_eq_of_r_eq_some h)).hom ≫
          (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).symm
            (omegaEvalToConstPresheaf Λ X n) ≫
          eqToHom (congrArg (fun j ↦ (Cotangent.constCotangentCochain Λ X).X j)
            (embeddingDownNat.f_eq_of_r_eq_some h))
    | none => 0
  comm' := sorry

/-- Unfolding of `omegaEvalToConstCotangent` in cohomological degree `-n`. -/
theorem omegaEvalToConstCotangent_f (n : ℕ) :
    (omegaEvalToConstCotangent Λ X).f (-n) =
      (omegaEvalSheafComplexXIso Λ X n).hom ≫
        (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).symm
          (omegaEvalToConstPresheaf Λ X n) :=
  sorry

/-- The derived comparison `Lπ_!(i^* Ω) ⟶ L_{O_X / underline{Λ}}`. -/
def omegaEvalToConstCotangentDerived :
    lowerShriekOmega Λ X ⟶ Cotangent.constCotangent Λ X :=
  DerivedCategory.Q.map (omegaEvalToConstCotangent Λ X)

/-- Unfolding of `omegaEvalToConstCotangentDerived`. -/
theorem omegaEvalToConstCotangentDerived_eq :
    omegaEvalToConstCotangentDerived Λ X =
      DerivedCategory.Q.map (omegaEvalToConstCotangent Λ X) :=
  sorry

/-- The derived comparison is an isomorphism in `D(O_X)`. -/
instance omegaEvalToConstCotangentDerived_isIso :
    IsIso (omegaEvalToConstCotangentDerived Λ X) :=
  sorry

/-- The canonical identification
`L_{X / Spec Λ} ≅ Lπ_!(i^* Ω_{O / underline{Λ}})` in `D(O_X)`. -/
def cotangentLowerShriekIso :
    DerivedCategory.Q.obj (Hom.cotangentComplex (X ↘ Spec Λ)) ≅ lowerShriekOmega Λ X :=
  Cotangent.overRingIso Λ X ≪≫ (asIso (omegaEvalToConstCotangentDerived Λ X)).symm

/-- The forward map of `cotangentLowerShriekIso` is `overRingIso` followed by the inverse
of the derived evaluation comparison. -/
theorem cotangentLowerShriekIso_hom :
    (cotangentLowerShriekIso Λ X).hom =
      (Cotangent.overRingIso Λ X).hom ≫ inv (omegaEvalToConstCotangentDerived Λ X) :=
  sorry

/-- Sheafification of `O`-modules preserves finite limits. -/
instance sheafification_structureSheaf_preservesFiniteLimits :
    PreservesFiniteLimits
      (PresheafOfModules.sheafification (𝟙 (structureSheaf Λ X).obj)) :=
  sorry

/-- Sheafification of `underline{O}_X`-modules preserves finite limits. -/
instance sheafification_inverseImage_preservesFiniteLimits :
    PreservesFiniteLimits
      (PresheafOfModules.sheafification (𝟙 (inverseImageStructureSheaf Λ X).obj)) :=
  sorry

/-- Module sheaves over `O` on `C_{X/Λ}` form an abelian category. -/
instance structureSheafModules_abelian :
    Abelian (SheafOfModules.{u} (structureSheaf Λ X)) :=
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheaf Λ X).obj)
  abelianOfAdjunction _ _ (asIso adj.counit) adj

/-- Module sheaves over `underline{O}_X` on `C_{X/Λ}` form an abelian category. -/
instance inverseImageStructureSheafModules_abelian :
    Abelian (SheafOfModules.{u} (inverseImageStructureSheaf Λ X)) :=
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (inverseImageStructureSheaf Λ X).obj)
  abelianOfAdjunction _ _ (asIso adj.counit) adj

/-- Module sheaves over `O` on `C_{X/Λ}` have a standard derived category. -/
instance structureSheafModules_hasDerivedCategory :
    HasDerivedCategory (SheafOfModules.{u} (structureSheaf Λ X)) :=
  HasDerivedCategory.standard _

/-- Module sheaves over `underline{O}_X` on `C_{X/Λ}` have a standard derived category. -/
instance inverseImageStructureSheafModules_hasDerivedCategory :
    HasDerivedCategory (SheafOfModules.{u} (inverseImageStructureSheaf Λ X)) :=
  HasDerivedCategory.standard _

/-- Same-site extension of scalars along `i♯` is additive. -/
instance extendScalars_structureSheafMap_additive :
    (SheafOfModules.ChangeOfRings.extendScalars (structureSheafMap Λ X)).Additive :=
  sorry

/-- Same-site extension of scalars along `i♯` admits an unbounded total left derived functor. -/
instance extendScalars_structureSheafMap_hasLeftDerived :
    (Functor.Homotopy.toDerived
        (SheafOfModules.ChangeOfRings.extendScalars
          (structureSheafMap Λ X))).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheaf Λ X))
        (ComplexShape.up ℤ)) :=
  sorry

/-- Derived inverse image `Li^*` along `i♯ : O ⟶ underline{O}_X`, as the total left
derived functor of same-site extension of scalars. -/
def derivedInverseImage :
    DerivedCategory (SheafOfModules.{u} (structureSheaf Λ X)) ⥤
      DerivedCategory (SheafOfModules.{u} (inverseImageStructureSheaf Λ X)) :=
  Functor.LeftDerived.Homotopy.functor
    (SheafOfModules.ChangeOfRings.extendScalars (structureSheafMap Λ X))

/-- Unfolding of `derivedInverseImage` as the homotopy total left derived functor of
extension of scalars along `i♯`. -/
theorem derivedInverseImage_eq :
    derivedInverseImage Λ X =
      Functor.LeftDerived.Homotopy.functor
        (SheafOfModules.ChangeOfRings.extendScalars (structureSheafMap Λ X)) :=
  sorry

/-- The cochain-level comparison `Li^* (omegaSheaf[0]) ⟶ (i^* omegaSheaf)[0]`, followed
by the underived identification with `omegaPullback`. -/
def derivedPullbackToOmega :
    (derivedInverseImage Λ X).obj
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheaf Λ X)) (0 : ℤ)).obj
          (omegaSheaf Λ X)) ⟶
      (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (inverseImageStructureSheaf Λ X)) (0 : ℤ)).obj
        (omegaPullback Λ X) :=
  (Functor.LeftDerived.Homotopy.cochainCounit
      (SheafOfModules.ChangeOfRings.extendScalars (structureSheafMap Λ X))).app
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (omegaSheaf Λ X)) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
          (SheafOfModules.ChangeOfRings.extendScalars (structureSheafMap Λ X))
          (ComplexShape.up ℤ) 0).hom.app (omegaSheaf Λ X)) ≫
    (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (inverseImageStructureSheaf Λ X)) (0 : ℤ)).map
      (omegaExtendToPullback Λ X)

/-- `derivedPullbackToOmega` is the cochain counit of `Li^*`, the single-complex
identification of extension of scalars, and `omegaExtendToPullback`. -/
theorem derivedPullbackToOmega_eq :
    derivedPullbackToOmega Λ X =
      (Functor.LeftDerived.Homotopy.cochainCounit
          (SheafOfModules.ChangeOfRings.extendScalars (structureSheafMap Λ X))).app
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (omegaSheaf Λ X)) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex
              (SheafOfModules.ChangeOfRings.extendScalars (structureSheafMap Λ X))
              (ComplexShape.up ℤ) 0).hom.app (omegaSheaf Λ X)) ≫
        (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (inverseImageStructureSheaf Λ X)) (0 : ℤ)).map
          (omegaExtendToPullback Λ X) :=
  sorry

/-- Because `Ω_{O / underline{Λ}}` is `O`-flat on polynomial algebras, the comparison
`Li^* omegaSheaf ⟶ omegaPullback` is an isomorphism in `D(underline{O}_X)`. -/
instance derivedPullbackToOmega_isIso : IsIso (derivedPullbackToOmega Λ X) :=
  sorry

/-- Because `Ω_{O / underline{Λ}}` is `O`-flat on every object of `C_{X/Λ}`,
`Li^* omegaSheaf = i^* omegaSheaf = omegaPullback` in `D(underline{O}_X)`. -/
def derivedPullbackIso :
    (derivedInverseImage Λ X).obj
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheaf Λ X)) (0 : ℤ)).obj
          (omegaSheaf Λ X)) ≅
      (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (inverseImageStructureSheaf Λ X)) (0 : ℤ)).obj
        (omegaPullback Λ X) :=
  asIso (derivedPullbackToOmega Λ X)

/-- The forward map of `derivedPullbackIso` is `derivedPullbackToOmega`. -/
theorem derivedPullbackIso_hom :
    (derivedPullbackIso Λ X).hom = derivedPullbackToOmega Λ X :=
  sorry

end AlgebraicGeometry.Scheme.CotangentSite
