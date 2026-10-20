/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Derived
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.Algebra.Homology.DerivedCategory.TensorProduct
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.TotalComplexShift
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Shift.Localization
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived
public import ReasLib.RingTheory.CotangentComplex.Atiyah.DerivedExtension

/-!
# The distinguished triangle of first principal parts in `D(B)`

For an `A`-algebra `B` and a `B`-module `M`, this module constructs the distinguished triangle
`L_{B/A} ⊗^L_B M ⟶ Lπ_!(P¹_{O / underline{A}}(M)) ⟶ M ⟶ (L_{B/A} ⊗^L_B M)⟦1⟧`
in `D(Mod B)`, obtained by applying derived tensor along `P_n → B` and Moore
evaluation to the genuine first principal-parts sequence of simplicial `P_•`-modules.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.MonoidalCategory
open HomologicalComplex
open AlgebraicTopology
open Opposite
open Algebra.CotangentComplex.Atiyah
open scoped CategoryTheory

noncomputable section

universe u

namespace Algebra.CotangentComplex.Atiyah

variable {R : Type u} [CommRing R]

/-- A homotopy-category arrow representing a derived-category morphism. -/
private def comparisonArrow {X Y : DerivedCategory (ModuleCat.{u} R)} (f : X ⟶ Y) :
    Arrow (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  DerivedCategory.Qh.mapArrow.objPreimage (Arrow.mk f)

/-- The localization of the representing homotopy arrow is isomorphic to the original arrow. -/
private def comparisonArrowIso {X Y : DerivedCategory (ModuleCat.{u} R)} (f : X ⟶ Y) :
    DerivedCategory.Qh.mapArrow.obj (comparisonArrow f) ≅ Arrow.mk f :=
  DerivedCategory.Qh.mapArrow.objObjPreimageIso (Arrow.mk f)

/-- The localization isomorphism of a quasi-isomorphism, with inverse given by its formal reverse edge. -/
private def homotopyFormalIso
    {K L : HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)} (f : K ⟶ L)
    (hf : HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ) f) :
    DerivedCategory.Qh.obj K ≅ DerivedCategory.Qh.obj L where
  hom := DerivedCategory.Qh.map f
  inv := Localization.homEquiv
    (HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).Q
    DerivedCategory.Qh (Localization.Construction.wInv f hf)
  hom_inv_id := by
    rw [Localization.Construction.wInv_eq_isoOfHom_inv,
      Localization.homEquiv_isoOfHom_inv]
    exact Localization.isoOfHom_hom_inv_id _ _ f hf
  inv_hom_id := by
    rw [Localization.Construction.wInv_eq_isoOfHom_inv,
      Localization.homEquiv_isoOfHom_inv]
    exact Localization.isoOfHom_inv_hom_id _ _ f hf

/-- A derived-category isomorphism obtained by localizing a quasi-isomorphic arrow representative. -/
private def comparisonFormalIso {X Y : DerivedCategory (ModuleCat.{u} R)} (f : X ⟶ Y)
    (hf : HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)
      (comparisonArrow f).hom) : X ≅ Y :=
  (Arrow.leftFunc.mapIso (comparisonArrowIso f)).symm ≪≫
    homotopyFormalIso (comparisonArrow f).hom hf ≪≫
    Arrow.rightFunc.mapIso (comparisonArrowIso f)

/-- The forward morphism of the localized comparison is the original morphism. -/
private theorem comparisonFormalIso_hom {X Y : DerivedCategory (ModuleCat.{u} R)} (f : X ⟶ Y)
    (hf : HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)
      (comparisonArrow f).hom) : (comparisonFormalIso f hf).hom = f := by
  exact (Arrow.iso_w (comparisonArrowIso f)).symm

/-- Coproducts along total-complex antidiagonals exist in `ModuleCat R`. -/
instance hasTotal_moduleCat_bicomplex
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) :
    K.HasTotal (ComplexShape.up ℤ) := by
  classical
  intro n
  exact HasColimit.mk ⟨ModuleCat.coproductCocone _, ModuleCat.coproductCoconeIsColimit _⟩

/-- The total-complex functor on bicomplexes of `R`-modules commutes with the outer shift. -/
instance totalFunctor_commShift :
    (HomologicalComplex₂.totalFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).CommShift ℤ := by
  refine {
    commShiftIso n :=
      NatIso.ofComponents
        (fun K => HomologicalComplex₂.totalShift₁Iso (x := n) (K := K))
        (fun _ => ?_)
    commShiftIso_zero := ?_
    commShiftIso_add _ _ := ?_
  }
  all_goals sorry

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The Moore cochain complex of a simplicial `B`-module. -/
def mooreExtend :
    (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) ⥤ CochainComplex (ModuleCat.{u} B) ℤ :=
  alternatingFaceMapComplex (ModuleCat.{u} B) ⋙
    ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} B)

/-- Moore evaluation is additive. -/
instance mooreExtend_additive : (mooreExtend B).Additive :=
  sorry

/-- Unfolding of `mooreExtend` as alternating faces followed by the integer embedding. -/
theorem mooreExtend_obj (N : SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) :
    (mooreExtend B).obj N =
      ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj N).extend
        ComplexShape.embeddingDownNat :=
  sorry

/-- Inclusion of the degree-zero row into the total complex of a single bicomplex. -/
def totalSingleι (K : CochainComplex (ModuleCat.{u} B) ℤ) (n : ℤ) :
    K.X n ⟶
      (HomologicalComplex₂.total
        ((HomologicalComplex.single (CochainComplex (ModuleCat.{u} B) ℤ)
            (ComplexShape.up ℤ) 0).obj K)
        (ComplexShape.up ℤ)).X n :=
  HomologicalComplex₂.ιTotal
    ((HomologicalComplex.single (CochainComplex (ModuleCat.{u} B) ℤ)
        (ComplexShape.up ℤ) 0).obj K)
    (ComplexShape.up ℤ) 0 n n (by change (0 : ℤ) + n = n; exact zero_add n)

/-- A totalized single row is identified with its sole nonzero summand by coproduct descent. -/
def totalSingleXIso (K : CochainComplex (ModuleCat.{u} B) ℤ) (n : ℤ) :
    K.X n ≅
      (HomologicalComplex₂.total
        ((HomologicalComplex.single (CochainComplex (ModuleCat.{u} B) ℤ)
          (ComplexShape.up ℤ) 0).obj K) (ComplexShape.up ℤ)).X n := by
  refine {
    hom := totalSingleι B K n
    inv := HomologicalComplex₂.totalDesc _ (fun i j h => by
      classical
      by_cases hi : i = 0
      · subst i
        have hj : j = n := by simpa using h
        subst j
        exact 𝟙 _
      · exact 0)
    hom_inv_id := ?_
    inv_hom_id := ?_
  }
  all_goals sorry

/-- The degree-zero row inclusion `totalSingleι` is invertible. -/
instance totalSingleι_isIso (K : CochainComplex (ModuleCat.{u} B) ℤ) (n : ℤ) :
    IsIso (totalSingleι B K n) :=
  (totalSingleXIso B K n).isIso_hom

/-- Totalization of a degree-zero single bicomplex recovers the original complex. -/
def totalSingleIso (K : CochainComplex (ModuleCat.{u} B) ℤ) :
    HomologicalComplex₂.total
        ((HomologicalComplex.single (CochainComplex (ModuleCat.{u} B) ℤ)
            (ComplexShape.up ℤ) 0).obj K)
        (ComplexShape.up ℤ) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (totalSingleXIso B K n).symm)
    (fun _ _ _ => sorry)

/-- Degreewise Moore evaluation of a complex of simplicial `B`-modules, then totalization. -/
def evaluationOnComplex :
    CochainComplex (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) ℤ ⥤
      DerivedCategory (ModuleCat.{u} B) :=
  (mooreExtend B).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex₂.totalFunctor (ModuleCat.{u} B) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q

/-- Moore totalization preserves quasi-isomorphisms of complexes of simplicial modules. -/
private theorem evaluationOnComplex_map_quasiIso
    {K L : CochainComplex (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) ℤ}
    (f : K ⟶ L) (hf : QuasiIso f) :
    QuasiIso (((mooreExtend B).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      HomologicalComplex₂.totalFunctor (ModuleCat.{u} B) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f) := sorry

/-- Moore totalization inverts quasi-isomorphisms of complexes of simplicial modules. -/
theorem evaluationOnComplex_inverts :
    (HomologicalComplex.quasiIso (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B)
        (ComplexShape.up ℤ)).IsInvertedBy
      (evaluationOnComplex B) := by
  intro K L f hf
  exact (Localization.isoOfHom DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ))
    (((mooreExtend B).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      HomologicalComplex₂.totalFunctor (ModuleCat.{u} B) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f)
    (evaluationOnComplex_map_quasiIso B f hf)).isIso_hom

/-- Derived Moore evaluation of simplicial modules by totalization. -/
def evaluation :
    DerivedCategory (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) ⥤
      DerivedCategory (ModuleCat.{u} B) :=
  CategoryTheory.Localization.lift
    (evaluationOnComplex B) (evaluationOnComplex_inverts B)
    (DerivedCategory.Q :
      CochainComplex (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) ℤ ⥤
        DerivedCategory (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B))

/-- Moore totalization of a complex of simplicial modules commutes with integer shifts. -/
instance evaluationOnComplex_commShift :
    (evaluationOnComplex B).CommShift ℤ :=
  inferInstanceAs
    (((mooreExtend B).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex₂.totalFunctor (ModuleCat.{u} B) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q).CommShift ℤ)

/-- Derived Moore evaluation is the localization lift of Moore totalization. -/
instance evaluation_lifting :
    Localization.Lifting
      (DerivedCategory.Q :
        CochainComplex (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) ℤ ⥤
          DerivedCategory (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B))
      (HomologicalComplex.quasiIso (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B)
        (ComplexShape.up ℤ))
      (evaluationOnComplex B) (evaluation B) :=
  Localization.liftingLift (evaluationOnComplex B) (evaluationOnComplex_inverts B)
    (DerivedCategory.Q :
      CochainComplex (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) ℤ ⥤
        DerivedCategory (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B))

/-- Derived Moore evaluation commutes with integer shifts. -/
instance evaluation_commShift :
    (evaluation B).CommShift ℤ :=
  Functor.commShiftOfLocalization
    (DerivedCategory.Q :
      CochainComplex (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) ℤ ⥤
        DerivedCategory (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B))
    (HomologicalComplex.quasiIso (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B)
      (ComplexShape.up ℤ))
    ℤ (evaluationOnComplex B) (evaluation B)

/-- Comparison `L(colim)(single N) ≅ Q(Moore N)` realized as Moore totalization of a single. -/
def evaluationSingleIso (N : SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) :
    (evaluation B).obj
        ((DerivedCategory.singleFunctor
            (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) 0).obj N) ≅
      DerivedCategory.Q.obj ((mooreExtend B).obj N) :=
  (evaluation B).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ
          (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) 0).app N) ≪≫
    (CategoryTheory.Localization.fac (evaluationOnComplex B)
        (evaluationOnComplex_inverts B)
        (DerivedCategory.Q :
          CochainComplex (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) ℤ ⥤
            DerivedCategory (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B))).app
      ((HomologicalComplex.single (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B)
          (ComplexShape.up ℤ) 0).obj N) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex₂.totalFunctor (ModuleCat.{u} B) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex (mooreExtend B)
            (ComplexShape.up ℤ) 0).app N)) ≪≫
    DerivedCategory.Q.mapIso (totalSingleIso B ((mooreExtend B).obj N))

/-- Derived lower shriek of a simplicial module by scalar extension along the augmentation and Moore evaluation. -/
def lowerShriek :
    DerivedCategory (PresheafOfModules.{u} (standardSimplicialRing A B)) ⥤
      DerivedCategory (ModuleCat.{u} B) :=
  derivedExtension A B ⋙ evaluation B

/-- Derived lower shriek commutes with integer shifts. -/
instance lowerShriek_commShift : (lowerShriek A B).CommShift ℤ :=
  inferInstanceAs ((derivedExtension A B ⋙ evaluation B).CommShift ℤ)

/-- The image of the genuine simplicial first principal-parts sequence under derived
lower shriek `Lπ_!`. -/
def triangleOfSES (M : ModuleCat.{u} B) :
    Triangle (DerivedCategory (ModuleCat.{u} B)) :=
  (lowerShriek A B).mapTriangle.obj
    (principalPartsSequence_shortExact A B M).singleTriangle

/-- Unfolding of `triangleOfSES` as `Lπ_!` applied to the principal-parts
`singleTriangle`. -/
theorem triangleOfSES_eq (M : ModuleCat.{u} B) :
    triangleOfSES A B M =
      (lowerShriek A B).mapTriangle.obj
        (principalPartsSequence_shortExact A B M).singleTriangle :=
  sorry

/-- The object `Lπ_!(P¹_{O / underline{A}}(M))` in `D(Mod B)`. -/
abbrev derivedPrincipalParts (M : ModuleCat.{u} B) :
    DerivedCategory (ModuleCat.{u} B) :=
  (lowerShriek A B).obj
    ((DerivedCategory.singleFunctor
        (PresheafOfModules.{u} (standardSimplicialRing A B)) 0).obj
      (principalPartsModule A B M))

/-- Unfolding of `derivedPrincipalParts` as `Lπ_!` of the degree-zero single of
`principalPartsModule`. -/
theorem derivedPrincipalParts_eq (M : ModuleCat.{u} B) :
    derivedPrincipalParts A B M =
      (lowerShriek A B).obj
        ((DerivedCategory.singleFunctor
            (PresheafOfModules.{u} (standardSimplicialRing A B)) 0).obj
          (principalPartsModule A B M)) :=
  sorry

/-- The standard-resolution model of `L_{B/A} ⊗_B M` in `D(Mod B)`. -/
abbrev tensorModule (M : ModuleCat.{u} B) : DerivedCategory (ModuleCat.{u} B) :=
  DerivedCategory.Q.obj (tensorCochain A B M)

/-- Unfolding of `tensorModule` as `Q` of the Moore complex of `simplicialCotangent`. -/
theorem tensorModule_eq (M : ModuleCat.{u} B) :
    tensorModule A B M = DerivedCategory.Q.obj (tensorCochain A B M) :=
  sorry

/-- Comparison `L(extend)(single X) ⟶ single (extend X)` from the homotopy-to-derived counit. -/
def derivedExtensionSingle
    (X : PresheafOfModules.{u} (standardSimplicialRing A B)) :
    (derivedExtension A B).obj
        ((DerivedCategory.singleFunctor
            (PresheafOfModules.{u} (standardSimplicialRing A B)) 0).obj X) ⟶
      (DerivedCategory.singleFunctor
          (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) 0).obj
        ((extensionDegreewise A B).obj X) :=
  (Functor.LeftDerived.Homotopy.counit (extensionDegreewise A B)).app
      ((HomotopyCategory.singleFunctor
          (PresheafOfModules.{u} (standardSimplicialRing A B)) 0).obj X) ≫
    (Functor.Homotopy.singleIso (extensionDegreewise A B) 0).hom.app X

/-- Degreewise comparison `extend(Ω_{P_n/A} ⊗ M) ⟶ (extend Ω_{P_n/A}) ⊗ M`. -/
def cotangentExtend (M : ModuleCat.{u} B) :
    (extensionDegreewise A B).obj (cotangentModule A B M) ⟶ simplicialCotangent A B M where
  app n :=
    (Functor.Monoidal.μIso (ModuleCat.extendScalars (augmentationHom A B n))
        (CommRingCat.KaehlerDifferential (standardTerm A B n).hom)
        (restrictModule A B M n)).inv ≫
      ((ModuleCat.extendScalars (augmentationHom A B n)).obj
          (CommRingCat.KaehlerDifferential (standardTerm A B n).hom) ◁
        (ModuleCat.extendRestrictScalarsAdj (augmentationHom A B n)).counit.app M)
  naturality := fun {X Y} f => sorry

/-- Degreewise reverse comparison `(extend Ω_{P_n/A}) ⊗ M ⟶ extend(Ω_{P_n/A} ⊗ M)`. -/
def cotangentExtendInv (M : ModuleCat.{u} B) :
    simplicialCotangent A B M ⟶
      (extensionDegreewise A B).obj (cotangentModule A B M) := by
  refine {
    app n :=
      -- Local instance justification (noncanonical choice): the augmentation P_n → B depends on n and selects the scalar action needed for the explicit tensor map m ↦ 1 ⊗ m.
      letI : Algebra (standardTerm A B n).right B := (augmentationHom A B n).toAlgebra
      ((ModuleCat.extendScalars (augmentationHom A B n)).obj
          (CommRingCat.KaehlerDifferential (standardTerm A B n).hom) ◁
        ModuleCat.ofHom
          { toFun := fun m : M =>
              (1 : B) ⊗ₜ[standardTerm A B n |>.right] m
            map_add' := ?_
            map_smul' := ?_ }) ≫
        (Functor.Monoidal.μIso (ModuleCat.extendScalars (augmentationHom A B n))
            (CommRingCat.KaehlerDifferential (standardTerm A B n).hom)
            (restrictModule A B M n)).hom
    naturality := fun {X Y} f => ?_
  }
  all_goals sorry

/-- Cochain-level comparison from the underived extension of `Ω ⊗ M` to `tensorCochain`. -/
def cotangentExtendCochain (M : ModuleCat.{u} B) :
    ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
        ((extensionDegreewise A B).obj (cotangentModule A B M))).extend
      ComplexShape.embeddingDownNat ⟶
      tensorCochain A B M :=
  HomologicalComplex.extendMap
    ((alternatingFaceMapComplex (ModuleCat.{u} B)).map (cotangentExtend A B M))
    ComplexShape.embeddingDownNat

/-- Cochain-level reverse comparison from `tensorCochain` to the underived extension of `Ω ⊗ M`. -/
def cotangentExtendInvCochain (M : ModuleCat.{u} B) :
    tensorCochain A B M ⟶
      ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
          ((extensionDegreewise A B).obj (cotangentModule A B M))).extend
        ComplexShape.embeddingDownNat :=
  HomologicalComplex.extendMap
    ((alternatingFaceMapComplex (ModuleCat.{u} B)).map (cotangentExtendInv A B M))
    ComplexShape.embeddingDownNat

/-- Simplicial comparison identifying `simplicialCotangent` with whiskering by `tensorRight M`. -/
def simplicialCotangentToWhisker (M : ModuleCat.{u} B) :
    simplicialCotangent A B M ⟶
      ((SimplicialObject.whiskering (ModuleCat.{u} B) (ModuleCat.{u} B)).obj
        (MonoidalCategory.tensorRight M)).obj
        (CommRingCat.Under.CotangentComplex.simplicialModule
          (CommRingCat.of A) (under A B)) where
  app n := 𝟙 _
  naturality := fun {X Y} f => sorry

/-- Reverse simplicial comparison from whiskering by `tensorRight M` to `simplicialCotangent`. -/
def simplicialWhiskerToCotangent (M : ModuleCat.{u} B) :
    ((SimplicialObject.whiskering (ModuleCat.{u} B) (ModuleCat.{u} B)).obj
        (MonoidalCategory.tensorRight M)).obj
        (CommRingCat.Under.CotangentComplex.simplicialModule
          (CommRingCat.of A) (under A B)) ⟶
      simplicialCotangent A B M where
  app n := 𝟙 _
  naturality := fun {X Y} f => sorry

/-- Degreewise tensor of the standard cotangent simplicial module with `M`, as a cochain
complex. -/
def cotangentTensorCochain (M : ModuleCat.{u} B) :
    CochainComplex (ModuleCat.{u} B) ℤ :=
  ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
      (((SimplicialObject.whiskering (ModuleCat.{u} B) (ModuleCat.{u} B)).obj
        (MonoidalCategory.tensorRight M)).obj
        (CommRingCat.Under.CotangentComplex.simplicialModule
          (CommRingCat.of A) (under A B)))).extend ComplexShape.embeddingDownNat

/-- Unfolding of `cotangentTensorCochain` as Moore evaluation of whiskered cotangent terms. -/
theorem cotangentTensorCochain_eq (M : ModuleCat.{u} B) :
    cotangentTensorCochain A B M =
      ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
          (((SimplicialObject.whiskering (ModuleCat.{u} B) (ModuleCat.{u} B)).obj
            (MonoidalCategory.tensorRight M)).obj
            (CommRingCat.Under.CotangentComplex.simplicialModule
              (CommRingCat.of A) (under A B)))).extend ComplexShape.embeddingDownNat :=
  sorry

/-- Cochain-level comparison `tensorCochain ⟶ cotangentComplex ⊗ M`. -/
def tensorCochainToCotangentTensor (M : ModuleCat.{u} B) :
    tensorCochain A B M ⟶ cotangentTensorCochain A B M :=
  HomologicalComplex.extendMap
    ((alternatingFaceMapComplex (ModuleCat.{u} B)).map
      (simplicialCotangentToWhisker A B M))
    ComplexShape.embeddingDownNat

/-- Cochain-level reverse comparison `cotangentComplex ⊗ M ⟶ tensorCochain`. -/
def cotangentTensorToTensorCochain (M : ModuleCat.{u} B) :
    cotangentTensorCochain A B M ⟶ tensorCochain A B M :=
  HomologicalComplex.extendMap
    ((alternatingFaceMapComplex (ModuleCat.{u} B)).map
      (simplicialWhiskerToCotangent A B M))
    ComplexShape.embeddingDownNat

/-- The counit of derived tensor against `M` at `Algebra.cotangentComplex` is invertible by
flatness of the standard-resolution terms. -/
instance derivedTensorCounit_isIso (M : ModuleCat.{u} B) :
    IsIso ((DerivedCategory.derivedTensorProductCounit
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M)).app
      ((HomotopyCategory.quotient (ModuleCat.{u} B) (ComplexShape.up ℤ)).obj
        (Algebra.cotangentComplex A B))) :=
  sorry

/-- The underived tensor-associativity comparison is invertible. -/
instance cotangentExtend_isIso (M : ModuleCat.{u} B) :
    IsIso (cotangentExtend A B M) :=
  sorry

/-- The counit `extendScalars (restrictScalars M) ⟶ M`, as a simplicial map. -/
def restrictedExtendCounit (M : ModuleCat.{u} B) :
    (extensionDegreewise A B).obj (restrictedModule A B M) ⟶ simplicialConstant A B M where
  app n :=
    (ModuleCat.extendRestrictScalarsAdj (augmentationHom A B n)).counit.app M
  naturality := fun {X Y} f => sorry

/-- Degreewise `B ⊗_{P_n} M ⟶ M` is invertible on the restriction of a `B`-module. -/
instance restrictedExtendCounit_isIso (M : ModuleCat.{u} B) :
    IsIso (restrictedExtendCounit A B M) :=
  sorry

/-- The inverse comparison `M ⟶ extendScalars (restrictScalars M)`, as a simplicial map. -/
def restrictedExtendUnit (M : ModuleCat.{u} B) :
    simplicialConstant A B M ⟶
      (extensionDegreewise A B).obj (restrictedModule A B M) := by
  refine {
    app n :=
      -- Local instance justification (noncanonical choice): the augmentation P_n → B depends on n and selects the scalar action needed for the explicit tensor map m ↦ 1 ⊗ m.
      letI : Algebra (standardTerm A B n).right B := (augmentationHom A B n).toAlgebra
      ModuleCat.ofHom
        { toFun := fun m : M => (1 : B) ⊗ₜ[standardTerm A B n |>.right] m
          map_add' := ?_
          map_smul' := ?_ }
    naturality := fun {X Y} f => ?_
  }
  all_goals sorry

/-- The evaluation complex of the constant simplicial module is isomorphic to its degree-zero single complex. -/
def constantIsoSingle (M : ModuleCat.{u} B) :
    DerivedCategory.Q.obj (constantComplex A B M) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M := by
  refine {
    hom := DerivedCategory.Q.map (constantToSingle A B M)
    inv := DerivedCategory.Q.map (singleToConstant A B M)
    hom_inv_id := ?_
    inv_hom_id := ?_
  }
  all_goals sorry

/-- `tensorCochain` vanishes in strictly positive cohomological degrees. -/
theorem isZero_tensorCochain_X_of_pos (M : ModuleCat.{u} B) {n : ℤ} (hn : 0 < n) :
    IsZero ((tensorCochain A B M).X n) :=
  sorry

/-- The ordinary tensor of `Algebra.cotangentComplex` with the degree-zero single of `M`
vanishes in strictly positive cohomological degrees. -/
theorem isZero_cotangentTensorSingle_X_of_pos (M : ModuleCat.{u} B) {n : ℤ} (hn : 0 < n) :
    IsZero ((Algebra.cotangentComplex A B ⊗
      (HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj M).X n) :=
  sorry

/-- The tensor with a degree-zero single has the displayed summand as its degreewise value. -/
def cotangentSingleTermIso (M : ModuleCat.{u} B) (n : ℤ) :
    ((Algebra.cotangentComplex A B).X n ⊗
      ((HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj M).X 0) ≅
      (Algebra.cotangentComplex A B ⊗
        (HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj M).X n := by
  refine {
    hom := HomologicalComplex.ιTensorObj (Algebra.cotangentComplex A B)
      ((HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj M)
      n 0 n (add_zero n)
    inv := HomologicalComplex.mapBifunctorDesc (fun i j h => by
      classical
      by_cases hj : j = 0
      · subst j
        have hi : i = n := by simpa using h
        subst i
        exact 𝟙 _
      · exact 0)
    hom_inv_id := ?_
    inv_hom_id := ?_
  }
  all_goals sorry

/-- The summand inclusion of `cotangentComplex.X n ⊗ M` into the tensor with the
degree-zero single of `M` is invertible. -/
instance ιTensorObj_cotangent_single_isIso (M : ModuleCat.{u} B) (n : ℤ) :
    IsIso (HomologicalComplex.ιTensorObj (Algebra.cotangentComplex A B)
      ((HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj M) n 0 n
      (add_zero n)) :=
  (cotangentSingleTermIso A B M n).isIso_hom

/-- The summand inclusion of `cotangentComplex.X (-n.natAbs) ⊗ M` into the tensor with the
degree-zero single of `M`. -/
def ιTensorCotangentSingle (M : ModuleCat.{u} B) (n : ℤ) (hn : n = -n.natAbs) :
    ((Algebra.cotangentComplex A B).X (-(n.natAbs : ℤ)) ⊗
      ((HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj M).X 0) ⟶
      (Algebra.cotangentComplex A B ⊗
        (HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj M).X n :=
  HomologicalComplex.ιTensorObj (Algebra.cotangentComplex A B)
    ((HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj M)
    (-(n.natAbs : ℤ)) 0 n (by change -(n.natAbs : ℤ) + 0 = n; simpa using hn.symm)

/-- The summand inclusion `ιTensorCotangentSingle` is invertible. -/
instance ιTensorCotangentSingle_isIso (M : ModuleCat.{u} B) (n : ℤ)
    (hn : n = -n.natAbs) :
    IsIso (ιTensorCotangentSingle A B M n hn) := by
  have inclusion_isIso (k : ℤ) (hk : k = n) :
      IsIso (HomologicalComplex.ιTensorObj (Algebra.cotangentComplex A B)
        ((HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj M)
        k 0 n (by simpa using hk)) := by
    subst k
    exact ιTensorObj_cotangent_single_isIso A B M n
  exact inclusion_isIso _ hn.symm

/-- Degreewise identification of `tensorCochain` with `cotangentComplex ⊗ single M`. -/
def tensorCochainXIsoTensorSingle (M : ModuleCat.{u} B) (n : ℤ) :
    (tensorCochain A B M).X n ≅
      (Algebra.cotangentComplex A B ⊗
        (HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj M).X n :=
  dite (0 < n)
    (fun hn =>
      IsZero.iso (isZero_tensorCochain_X_of_pos A B M hn)
        (isZero_cotangentTensorSingle_X_of_pos A B M hn))
    (fun hn =>
      have hn' : n = -n.natAbs := by
        rw [Int.ofNat_natAbs_of_nonpos (le_of_not_gt hn), neg_neg]
      HomologicalComplex.XIsoOfEq (tensorCochain A B M) hn' ≪≫
      tensorCochain_X A B M n.natAbs ≪≫
      (MonoidalCategory.tensorRight M).mapIso
        (CommRingCat.Under.CotangentComplex.objXIso (CommRingCat.of A)
          (under A B) n.natAbs).symm ≪≫
      (whiskerLeftIso ((Algebra.cotangentComplex A B).X (-(n.natAbs : ℤ)))
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).symm) ≪≫
      (cotangentSingleTermIso A B M (-(n.natAbs : ℤ)) ≪≫
        HomologicalComplex.XIsoOfEq
          (Algebra.cotangentComplex A B ⊗
            (HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj M)
          hn'.symm))

/-- Cochain-level identification `tensorCochain ≅ cotangentComplex ⊗ single M`. -/
def tensorCochainIsoTensorSingle (M : ModuleCat.{u} B) :
    tensorCochain A B M ≅
      Algebra.cotangentComplex A B ⊗
        (HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj M :=
  HomologicalComplex.Hom.isoOfComponents (tensorCochainXIsoTensorSingle A B M)
    (fun _ _ _ => sorry)

/-- The actual derived-tensor counit is represented by a quasi-isomorphism for the cotangent complex. -/
private theorem counitAppOfQ_cotangent_single_quasiIso (M : ModuleCat.{u} B) :
    HomotopyCategory.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)
      (comparisonArrow (DerivedCategory.DerivedTensor.Bifunctor.counitAppOfQ
        (Algebra.cotangentComplex A B)
        ((HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj M))).hom :=
  sorry

/-- The two-variable derived-tensor counit at the standard cotangent complex against `M`
is invertible by flatness of the polynomial-resolution terms. -/
instance counitAppOfQ_cotangent_single_isIso (M : ModuleCat.{u} B) :
    IsIso (DerivedCategory.DerivedTensor.Bifunctor.counitAppOfQ
      (Algebra.cotangentComplex A B)
      ((HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj M)) := by
  simpa only [comparisonFormalIso_hom] using
    (comparisonFormalIso _ (counitAppOfQ_cotangent_single_quasiIso A B M)).isIso_hom

/-- The comparison `L_{B/A} ⊗_B M ≅ L_{B/A} ⊗^L_B M` using flatness of the standard terms. -/
def tensorModule_iso_derived (M : ModuleCat.{u} B) :
    tensorModule A B M ≅
      (DerivedCategory.derivedTensorProduct
          ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M)).obj
        (DerivedCategory.Q.obj (Algebra.cotangentComplex A B)) := by
  let f := DerivedCategory.DerivedTensor.Bifunctor.counitAppOfQ
    (Algebra.cotangentComplex A B)
    ((HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj M)
  let a := DerivedCategory.Qh.mapArrow.objPreimage (Arrow.mk f)
  let e := DerivedCategory.Qh.mapArrow.objObjPreimageIso (Arrow.mk f)
  have hf : HomotopyCategory.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ) a.hom :=
    (DerivedCategory.isIso_Qh_map_iff a.hom).mp
      ((Arrow.isIso_hom_iff_isIso_of_isIso e.hom).mpr
        (counitAppOfQ_cotangent_single_isIso A B M))
  let localized : DerivedCategory.Qh.obj a.left ≅ DerivedCategory.Qh.obj a.right := {
    hom := DerivedCategory.Qh.map a.hom
    inv := Localization.homEquiv
      (HomotopyCategory.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)).Q
      DerivedCategory.Qh (Localization.Construction.wInv a.hom hf)
    hom_inv_id := by
      rw [Localization.Construction.wInv_eq_isoOfHom_inv,
        Localization.homEquiv_isoOfHom_inv]
      exact Localization.isoOfHom_hom_inv_id _ _ a.hom hf
    inv_hom_id := by
      rw [Localization.Construction.wInv_eq_isoOfHom_inv,
        Localization.homEquiv_isoOfHom_inv]
      exact Localization.isoOfHom_inv_hom_id _ _ a.hom hf
  }
  exact DerivedCategory.Q.mapIso (tensorCochainIsoTensorSingle A B M) ≪≫
    ((Arrow.leftFunc.mapIso e).symm ≪≫ localized ≪≫ Arrow.rightFunc.mapIso e).symm ≪≫
    (DerivedCategory.DerivedTensor.Bifunctor.leftFunctor
        (DerivedCategory.Q.obj (Algebra.cotangentComplex A B))).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} B) 0).app M).symm ≪≫
    (DerivedCategory.DerivedTensorProduct.objIsoBifunctor
        (DerivedCategory.Q.obj (Algebra.cotangentComplex A B))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M)).symm

/-- The derived-extension counit on the cotangent tensor becomes a quasi-isomorphism after Moore totalization. -/
theorem cotangentComparison_quasiIso (M : ModuleCat.{u} B) :
    HomotopyCategory.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)
      (DerivedCategory.Qh.mapArrow.objPreimage
        (Arrow.mk ((evaluation B).map
          (derivedExtensionSingle A B (cotangentModule A B M))))).hom :=
  sorry

/-- The evaluated cotangent comparison is invertible. -/
instance derivedExtensionSingle_cotangentModule_evaluation_isIso (M : ModuleCat.{u} B) :
    IsIso ((evaluation B).map (derivedExtensionSingle A B (cotangentModule A B M))) := by
  simpa only [comparisonFormalIso_hom] using
    (comparisonFormalIso _ (cotangentComparison_quasiIso A B M)).isIso_hom

/-- The formal localization inverse of the evaluated cotangent comparison. -/
def derivedExtensionSingle_cotangentModule_evaluation_inv (M : ModuleCat.{u} B) :
    (evaluation B).obj
        ((DerivedCategory.singleFunctor
            (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) 0).obj
          ((extensionDegreewise A B).obj (cotangentModule A B M))) ⟶
      (evaluation B).obj
        ((derivedExtension A B).obj
          ((DerivedCategory.singleFunctor
              (PresheafOfModules.{u} (standardSimplicialRing A B)) 0).obj
            (cotangentModule A B M))) :=   let f := (evaluation B).map (derivedExtensionSingle A B (cotangentModule A B M))
  let a := DerivedCategory.Qh.mapArrow.objPreimage (Arrow.mk f)
  let e := DerivedCategory.Qh.mapArrow.objObjPreimageIso (Arrow.mk f)
  (Arrow.rightFunc.mapIso e).inv ≫
    (Localization.homEquiv
      (HomotopyCategory.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)).Q
      DerivedCategory.Qh
      (Localization.Construction.wInv a.hom (cotangentComparison_quasiIso A B M)) ≫
    (Arrow.leftFunc.mapIso e).hom)

/-- The derived-extension counit on the restricted constant module becomes a quasi-isomorphism after Moore totalization. -/
theorem restrictedComparison_quasiIso (M : ModuleCat.{u} B) :
    HomotopyCategory.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)
      (DerivedCategory.Qh.mapArrow.objPreimage
        (Arrow.mk ((evaluation B).map
          (derivedExtensionSingle A B (restrictedModule A B M))))).hom :=
  sorry

/-- Invertibility of the constant-module comparison follows from its formal inverse. -/
instance derivedExtensionSingle_restrictedModule_evaluation_isIso (M : ModuleCat.{u} B) :
    IsIso ((evaluation B).map (derivedExtensionSingle A B (restrictedModule A B M))) := by
  simpa only [comparisonFormalIso_hom] using
    (comparisonFormalIso _ (restrictedComparison_quasiIso A B M)).isIso_hom

/-- The formal localization inverse of the evaluated constant-module comparison. -/
def derivedExtensionSingle_restrictedModule_evaluation_inv (M : ModuleCat.{u} B) :
    (evaluation B).obj
        ((DerivedCategory.singleFunctor
            (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) 0).obj
          ((extensionDegreewise A B).obj (restrictedModule A B M))) ⟶
      (evaluation B).obj
        ((derivedExtension A B).obj
          ((DerivedCategory.singleFunctor
              (PresheafOfModules.{u} (standardSimplicialRing A B)) 0).obj
            (restrictedModule A B M))) :=   let f := (evaluation B).map (derivedExtensionSingle A B (restrictedModule A B M))
  let a := DerivedCategory.Qh.mapArrow.objPreimage (Arrow.mk f)
  let e := DerivedCategory.Qh.mapArrow.objObjPreimageIso (Arrow.mk f)
  (Arrow.rightFunc.mapIso e).inv ≫
    (Localization.homEquiv
      (HomotopyCategory.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)).Q
      DerivedCategory.Qh
      (Localization.Construction.wInv a.hom (restrictedComparison_quasiIso A B M)) ≫
    (Arrow.leftFunc.mapIso e).hom)

/-- The cotangent formal inverse is a right inverse to the original evaluated counit. -/
theorem cotangentComparison_hom_inv_id (M : ModuleCat.{u} B) :
    (evaluation B).map (derivedExtensionSingle A B (cotangentModule A B M)) ≫
      derivedExtensionSingle_cotangentModule_evaluation_inv A B M = 𝟙 _ := by
  have h := (comparisonFormalIso _ (cotangentComparison_quasiIso A B M)).hom_inv_id
  rw [comparisonFormalIso_hom] at h
  unfold derivedExtensionSingle_cotangentModule_evaluation_inv at ⊢
  unfold comparisonFormalIso homotopyFormalIso comparisonArrowIso comparisonArrow at h
  simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc] at h ⊢
  with_unfolding_all exact h

/-- The cotangent formal inverse is a left inverse to the original evaluated counit. -/
theorem cotangentComparison_inv_hom_id (M : ModuleCat.{u} B) :
    derivedExtensionSingle_cotangentModule_evaluation_inv A B M ≫
      (evaluation B).map (derivedExtensionSingle A B (cotangentModule A B M)) = 𝟙 _ := by
  have h := (comparisonFormalIso _ (cotangentComparison_quasiIso A B M)).inv_hom_id
  rw [comparisonFormalIso_hom] at h
  unfold derivedExtensionSingle_cotangentModule_evaluation_inv at ⊢
  unfold comparisonFormalIso homotopyFormalIso comparisonArrowIso comparisonArrow at h
  simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc] at h ⊢
  with_unfolding_all exact h

/-- The constant-module formal inverse is a right inverse to the specified comparison. -/
theorem restrictedComparison_hom_inv_id (M : ModuleCat.{u} B) :
    (evaluation B).map (derivedExtensionSingle A B (restrictedModule A B M)) ≫
      derivedExtensionSingle_restrictedModule_evaluation_inv A B M = 𝟙 _ := by
  have h := (comparisonFormalIso _ (restrictedComparison_quasiIso A B M)).hom_inv_id
  rw [comparisonFormalIso_hom] at h
  unfold derivedExtensionSingle_restrictedModule_evaluation_inv at ⊢
  unfold comparisonFormalIso homotopyFormalIso comparisonArrowIso comparisonArrow at h
  simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc] at h ⊢
  with_unfolding_all exact h

/-- The constant-module formal inverse is a left inverse to the specified comparison. -/
theorem restrictedComparison_inv_hom_id (M : ModuleCat.{u} B) :
    derivedExtensionSingle_restrictedModule_evaluation_inv A B M ≫
      (evaluation B).map (derivedExtensionSingle A B (restrictedModule A B M)) = 𝟙 _ := by
  have h := (comparisonFormalIso _ (restrictedComparison_quasiIso A B M)).inv_hom_id
  rw [comparisonFormalIso_hom] at h
  unfold derivedExtensionSingle_restrictedModule_evaluation_inv at ⊢
  unfold comparisonFormalIso homotopyFormalIso comparisonArrowIso comparisonArrow at h
  simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc] at h ⊢
  with_unfolding_all exact h

/-- Derived lower shriek of the simplicial cotangent tensor is isomorphic to the standard cotangent tensor model. -/
def tensorIso (M : ModuleCat.{u} B) :
    (triangleOfSES A B M).obj₁ ≅ tensorModule A B M := by
  refine {
    hom :=
      (evaluation B).map (derivedExtensionSingle A B (cotangentModule A B M)) ≫
        (evaluation B).map
          ((DerivedCategory.singleFunctor
              (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) 0).map
            (cotangentExtend A B M)) ≫
        (evaluationSingleIso B (simplicialCotangent A B M)).hom
    inv :=
      (evaluationSingleIso B (simplicialCotangent A B M)).inv ≫
        (evaluation B).map
          ((DerivedCategory.singleFunctor
              (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) 0).map
            (cotangentExtendInv A B M)) ≫
        derivedExtensionSingle_cotangentModule_evaluation_inv A B M
    hom_inv_id := ?_
    inv_hom_id := ?_
  }
  all_goals sorry

/-- Derived lower shriek of the restricted constant module is isomorphic to the degree-zero single module. -/
def moduleIso (M : ModuleCat.{u} B) :
    (triangleOfSES A B M).obj₃ ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M := by
  refine {
    hom :=
      (evaluation B).map (derivedExtensionSingle A B (restrictedModule A B M)) ≫
        (evaluation B).map
          ((DerivedCategory.singleFunctor
              (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) 0).map
            (restrictedExtendCounit A B M)) ≫
        (evaluationSingleIso B (simplicialConstant A B M)).hom ≫
        (constantIsoSingle A B M).hom
    inv :=
      (constantIsoSingle A B M).inv ≫
        (evaluationSingleIso B (simplicialConstant A B M)).inv ≫
        (evaluation B).map
          ((DerivedCategory.singleFunctor
              (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) 0).map
            (restrictedExtendUnit A B M)) ≫
        derivedExtensionSingle_restrictedModule_evaluation_inv A B M
    hom_inv_id := ?_
    inv_hom_id := ?_
  }
  all_goals sorry

/-- The first map `Lπ_!(Ω_{P_•/A} ⊗ M) ⟶ Lπ_!(P¹_{O / underline{A}}(M))` of the displayed
triangle. -/
def tensorToPrincipalParts (M : ModuleCat.{u} B) :
    tensorModule A B M ⟶ derivedPrincipalParts A B M :=
  (tensorIso A B M).inv ≫ (triangleOfSES A B M).mor₁

/-- Unfolding of `tensorToPrincipalParts` by conjugating the SES-triangle first map. -/
theorem tensorToPrincipalParts_eq (M : ModuleCat.{u} B) :
    tensorToPrincipalParts A B M =
      (tensorIso A B M).inv ≫ (triangleOfSES A B M).mor₁ :=
  sorry

/-- The second map `Lπ_!(P¹_{O / underline{A}}(M)) ⟶ M` of the displayed triangle. -/
def principalPartsToModule (M : ModuleCat.{u} B) :
    derivedPrincipalParts A B M ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M :=
  (triangleOfSES A B M).mor₂ ≫ (moduleIso A B M).hom

/-- Unfolding of `principalPartsToModule` by conjugating the SES-triangle second map. -/
theorem principalPartsToModule_eq (M : ModuleCat.{u} B) :
    principalPartsToModule A B M =
      (triangleOfSES A B M).mor₂ ≫ (moduleIso A B M).hom :=
  sorry

/-- The connecting map `M ⟶ (L_{B/A} ⊗^L_B M)⟦1⟧` of the displayed triangle. -/
def connectingMap (M : ModuleCat.{u} B) :
    (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M ⟶
      (tensorModule A B M)⟦(1 : ℤ)⟧ :=
  (moduleIso A B M).inv ≫
    (triangleOfSES A B M).mor₃ ≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} B)) (1 : ℤ)).map (tensorIso A B M).hom

/-- Unfolding of `connectingMap` by conjugating the SES-triangle connecting map. -/
theorem connectingMap_eq (M : ModuleCat.{u} B) :
    connectingMap A B M =
      (moduleIso A B M).inv ≫
        (triangleOfSES A B M).mor₃ ≫
          (shiftFunctor (DerivedCategory (ModuleCat.{u} B)) (1 : ℤ)).map
            (tensorIso A B M).hom :=
  sorry

/-- The image of the genuine `P`-module first principal-parts sequence under derived
extension of scalars along a single map `P → B`. -/
def derivedBaseChangeTriangle {P : Type u} [CommRing P] (σ : A →+* P) (τ : P →+* B)
    (M : ModuleCat.{u} B) :
    Triangle (DerivedCategory (ModuleCat.{u} B)) :=
  (ModuleCat.derivedExtensionOfScalars τ).mapTriangle.obj
    (PrincipalParts.RingHom.FirstOrder.shortExact σ
      ((ModuleCat.restrictScalars τ).obj M)).singleTriangle

/-- Unfolding of `derivedBaseChangeTriangle` as `derivedExtensionOfScalars` applied to
the `P`-module `singleTriangle`. -/
theorem derivedBaseChangeTriangle_eq {P : Type u} [CommRing P] (σ : A →+* P)
    (τ : P →+* B) (M : ModuleCat.{u} B) :
    derivedBaseChangeTriangle A B σ τ M =
      (ModuleCat.derivedExtensionOfScalars τ).mapTriangle.obj
        (PrincipalParts.RingHom.FirstOrder.shortExact σ
          ((ModuleCat.restrictScalars τ).obj M)).singleTriangle :=
  sorry

/-- The displayed distinguished triangle
`L_{B/A} ⊗^L_B M ⟶ Lπ_!(P¹_{O / underline{A}}(M)) ⟶ M ⟶ (L_{B/A} ⊗^L_B M)⟦1⟧`
in `D(Mod B)`. -/
def triangle (M : ModuleCat.{u} B) : Triangle (DerivedCategory (ModuleCat.{u} B)) :=
  Triangle.mk (tensorToPrincipalParts A B M) (principalPartsToModule A B M)
    (connectingMap A B M)

/-- The first vertex of `triangle` is `tensorModule`. -/
theorem triangle_obj₁ (M : ModuleCat.{u} B) :
    (triangle A B M).obj₁ = tensorModule A B M :=
  sorry

/-- The second vertex of `triangle` is `derivedPrincipalParts`. -/
theorem triangle_obj₂ (M : ModuleCat.{u} B) :
    (triangle A B M).obj₂ = derivedPrincipalParts A B M :=
  sorry

/-- The third vertex of `triangle` is the degree-zero single complex of `M`. -/
theorem triangle_obj₃ (M : ModuleCat.{u} B) :
    (triangle A B M).obj₃ =
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M :=
  sorry

/-- The first morphism of `triangle` is `tensorToPrincipalParts`. -/
theorem triangle_mor₁ (M : ModuleCat.{u} B) :
    (triangle A B M).mor₁ = tensorToPrincipalParts A B M :=
  sorry

/-- The second morphism of `triangle` is `principalPartsToModule`. -/
theorem triangle_mor₂ (M : ModuleCat.{u} B) :
    (triangle A B M).mor₂ = principalPartsToModule A B M :=
  sorry

/-- The third morphism of `triangle` is `connectingMap`. -/
theorem triangle_mor₃ (M : ModuleCat.{u} B) :
    (triangle A B M).mor₃ = connectingMap A B M :=
  sorry

/-- The first principal-parts triangle is distinguished in `D(B)`. -/
theorem triangle_distinguished (M : ModuleCat.{u} B) :
    triangle A B M ∈ distTriang (DerivedCategory (ModuleCat.{u} B)) :=
  sorry

end Algebra.CotangentComplex.Atiyah

end
