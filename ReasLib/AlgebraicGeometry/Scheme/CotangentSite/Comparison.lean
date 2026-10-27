/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Single
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived
public import ReasLib.RingTheory.CotangentComplex.Functoriality
public import ReasLib.AlgebraicGeometry.Scheme.Module.CotangentComplex.OverRing
public import ReasLib.AlgebraicGeometry.Scheme.CotangentSite.NaiveDifferentials
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.Homology
public import ReasLib.AlgebraicGeometry.Scheme.CotangentSite.StandardResolution

/-!
# Evaluation of `i^* Ω` on standard fibrewise affine spaces

This module constructs the explicit complex `Lπ_!(Ω_{O / underline{Λ}} ⊗_O underline{O}_X)`
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

/-- The raw tensor differential module evaluated on a standard polynomial affine diagram. -/
def omegaEvalSiteObj (n : ℕ) (U : X.smallZariskiSite) :
    ModuleCat.{u} (sectionsRing Λ X U) :=
  omegaPullbackObj Λ X (standardAffine Λ X ⦋n⦌ U)

/-- Restriction of `omegaEvalSiteObj` along a morphism of the small Zariski site. -/
def omegaEvalSiteMap (n : ℕ) {V U : X.smallZariskiSite} (f : V ⟶ U) :
    omegaEvalSiteObj Λ X n U ⟶
      (ModuleCat.restrictScalars (sectionsRestrict Λ X f).hom).obj
        (omegaEvalSiteObj Λ X n V) :=
  omegaPullbackMap Λ X (standardAffineRestrict Λ X f ⦋n⦌).op

/-- Simplicial operators of `A_{•,U}` act on `omegaEvalSiteObj`. -/
def omegaEvalSiteSimplicialMap {n m : SimplexCategory} (f : n ⟶ m)
    (U : X.smallZariskiSite) :
    omegaEvalSiteObj Λ X m.len U ⟶
      (ModuleCat.restrictScalars
        ((inverseImageStructurePresheafComm Λ X).map
          (standardAffineHom Λ X f U).op).hom).obj
        (omegaEvalSiteObj Λ X n.len U) :=
  omegaPullbackMap Λ X (standardAffineHom Λ X f U).op

/-- Transport of `omegaEvalSiteObj` from the small Zariski site to an open of `X`. -/
def omegaEvalPresheafObj (n : ℕ) (U : X.Opensᵒᵖ) :
    ModuleCat.{u} (X.ringCatSheaf.obj.obj U) :=
  (ModuleCat.extendScalars ((X.restrictFunctorΓ).hom.app U).hom).obj
    (omegaEvalSiteObj Λ X n ((smallZariskiOpenFunctor X).obj U.unop))

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

/-- The presheaf of `O_X`-modules `U ↦ (i^* Ω)(A_{n,U})`. -/
def omegaEvalPresheaf (n : ℕ) : _root_.PresheafOfModules.{u} (X.ringCatSheaf.obj) := by
  refine { obj := fun U ↦ omegaEvalPresheafObj Λ X n U
           map := fun f ↦ omegaEvalPresheafMap Λ X n f
           map_id := ?_
           map_comp := ?_ }
  all_goals sorry

/-- Evaluating `omegaEvalPresheaf` at an open recovers `omegaEvalPresheafObj`. -/
theorem omegaEvalPresheaf_obj (n : ℕ) (U : X.Opens) :
    (omegaEvalPresheaf Λ X n).obj (op U) = omegaEvalPresheafObj Λ X n (op U) := rfl

/-- Sheafification of `U ↦ (i^* Ω)(A_{n,U})` as an object of `X.Modules`. -/
def omegaEvalSheaf (n : ℕ) : X.Modules :=
  (RingedSpace.moduleSheafification X.toRingedSpace).obj (omegaEvalPresheaf Λ X n)

/-- Simplicial operators of `A_{•,U}` act as the identity on `O_X(U)`. -/
theorem omegaEvalPresheafSimplicial_restrict_eq {n m : SimplexCategory} (f : n ⟶ m)
    (U : X.smallZariskiSite) :
    ((inverseImageStructurePresheafComm Λ X).map (standardAffineHom Λ X f U).op).hom =
      RingHom.id (sectionsRing Λ X U) :=
  sorry

/-- Simplicial operators act on `omegaEvalPresheaf`. -/
def omegaEvalPresheafSimplicialMap {n m : SimplexCategory} (f : n ⟶ m) :
    omegaEvalPresheaf Λ X m.len ⟶ omegaEvalPresheaf Λ X n.len where
  app U :=
    (ModuleCat.extendScalars ((X.restrictFunctorΓ).hom.app U).hom).map
        (omegaEvalSiteSimplicialMap Λ X f ((smallZariskiOpenFunctor X).obj U.unop) ≫
          (ModuleCat.restrictScalarsId'
              ((inverseImageStructurePresheafComm Λ X).map
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
              ((inverseImageStructurePresheafComm Λ X).map
                  (standardAffineHom Λ X f
                    ((smallZariskiOpenFunctor X).obj U.unop)).op).hom
              (omegaEvalPresheafSimplicial_restrict_eq Λ X f
                ((smallZariskiOpenFunctor X).obj U.unop))).hom.app _) := rfl

/-- The simplicial object in `X.Modules` obtained by sheafifying `U ↦ (i^* Ω)(A_{•,U})`. -/
def omegaEvalSimplicial : SimplicialObject X.Modules := by
  refine { obj := fun n ↦ omegaEvalSheaf Λ X n.unop.len
           map := fun f ↦ (RingedSpace.moduleSheafification X.toRingedSpace).map
             (omegaEvalPresheafSimplicialMap Λ X f.unop)
           map_id := ?_
           map_comp := ?_ }
  all_goals sorry

/-- Degree `n` of `omegaEvalSimplicial` is `omegaEvalSheaf n`. -/
theorem omegaEvalSimplicial_obj (n : SimplexCategoryᵒᵖ) :
    (omegaEvalSimplicial Λ X).obj n = omegaEvalSheaf Λ X n.unop.len := rfl

/-- The cochain complex of `O_X`-modules whose term in cohomological degree `-n` is the
sheafification of `U ↦ (i^* Ω)(A_{n,U})`. -/
def omegaEvalSheafComplex : CochainComplex X.Modules ℤ :=
  ((alternatingFaceMapComplex X.Modules).obj (omegaEvalSimplicial Λ X)).extend
    embeddingDownNat

/-- In cohomological degree `-n`, `omegaEvalSheafComplex` is `omegaEvalSheaf n`. -/
theorem omegaEvalSheafComplex_X (n : ℕ) :
    (omegaEvalSheafComplex Λ X).X (-n) = omegaEvalSheaf Λ X n :=
  sorry

/-- The object `Lπ_!(i^* Ω_{O / underline{Λ}})` in `D(O_X)`. -/
def lowerShriekOmega : DerivedCategory X.Modules :=
  DerivedCategory.Q.obj (omegaEvalSheafComplex Λ X)

/-- Global sections of `A_{n,U}` map to the polynomial model of `P_{n,U}` by the
Gamma-Spec identification. -/
def omegaEvalToPolynomial (n : ℕ) (U : X.smallZariskiSite) :
    Γ((standardAffine Λ X ⦋n⦌ U).right.obj.left, ⊤) ⟶ (standardPolynomial Λ X ⦋n⦌ U).right :=
  (Scheme.ΓSpecIso (standardPolynomial Λ X ⦋n⦌ U).right).hom

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
    Γ((standardAffine Λ X ⦋n⦌ U).right.obj.left, ⊤) ⟶
      (CommRingCat.Under.CotangentComplex.standardTerm Λ
        (standardAlgebra Λ X U) (op ⦋n⦌)).right :=
  omegaEvalToPolynomial Λ X n U ≫ omegaEvalPolynomialToStandard Λ X n U

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
      (standardAffine Λ X ⦋n⦌ U).hom.left.appTop.hom :=
  sorry

/-- Fibrewise naive differentials on `A_{n,U}` map to the degree-`n` standard-resolution
term of `L_{O_X(U) / Λ}`. -/
def omegaEvalSiteToSimplicial (n : ℕ) (U : X.smallZariskiSite) :
    omegaEvalSiteObj Λ X n U ⟶
      (CommRingCat.Under.CotangentComplex.simplicialModule Λ
        (standardAlgebra Λ X U)).obj (op ⦋n⦌) :=
  ((ModuleCat.extendRestrictScalarsAdj
      (standardAffine Λ X ⦋n⦌ U).hom.left.appTop.hom).homEquiv _ _).symm
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
          (standardAffine Λ X ⦋n⦌ U).hom.left.appTop.hom
          (omegaEvalAugmentation_comp Λ X n U).symm).inv.app _)

/-- The sheafification-unit component `Λ ⟶ underline{Λ}(U)` on the Zariski site of `X`. -/
def constRingSheafUnitApp (U : X.Opensᵒᵖ) :
    Λ ⟶ (Cotangent.constRingSheaf Λ X).obj.obj U :=
  ((sheafificationAdjunction (Opens.grothendieckTopology X.toTopCat) CommRingCat.{u}).unit.app
      ((Functor.const (TopologicalSpace.Opens X.toTopCat)ᵒᵖ).obj Λ)).app U

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
            (sectionsHom_restrictFunctorΓ Λ X U)).f i) := rfl

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
            (Cotangent.constToStructure Λ X) U).f (-n) := rfl

/-- The cohomological degree `-n` term of `omegaEvalSheafComplex` is `omegaEvalSheaf n`. -/
def omegaEvalSheafComplexXIso (n : ℕ) :
    (omegaEvalSheafComplex Λ X).X (-n) ≅ omegaEvalSheaf Λ X n :=
  extendXIso
    ((alternatingFaceMapComplex X.Modules).obj (omegaEvalSimplicial Λ X))
    embeddingDownNat
    (rfl : embeddingDownNat.f n = -n)

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
      (Cotangent.overRingIso Λ X).hom ≫ inv (omegaEvalToConstCotangentDerived Λ X) := rfl


end AlgebraicGeometry.Scheme.CotangentSite
