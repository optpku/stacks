/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.TotalComplexShift
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Shift.Localization
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.Connected
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived
public import stacks_project.Chap92.«92_17_0_1_PrincipalParts»

/-!
# The distinguished triangle of first principal parts in `D(B)`

For an `A`-algebra `B` and a `B`-module `M`, this module owns the distinguished triangle
`L_{B/A} ⊗^L_B M ⟶ Lπ_!(P¹_{O / underline{A}}(M)) ⟶ M ⟶ (L_{B/A} ⊗^L_B M)⟦1⟧`
in `D(Mod B)`, obtained by applying derived tensor along `P_n → B` and Lemma 92.4.1
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

/-- A representative of the specified derived comparison in the homotopy arrow category.
Its existence is Mathlib's proved essential surjectivity of `Qh.mapArrow`, independent
of any assertion that the specified comparison is invertible. -/
def comparisonArrow {X Y : DerivedCategory (ModuleCat.{u} R)} (f : X ⟶ Y) :
    Arrow (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  DerivedCategory.Qh.mapArrow.objPreimage (Arrow.mk f)

/-- The chosen representative presents the original arrow, including its endpoints
and its commutative square; it is not an arbitrary isomorphism of the endpoints. -/
def comparisonArrowIso {X Y : DerivedCategory (ModuleCat.{u} R)} (f : X ⟶ Y) :
    DerivedCategory.Qh.mapArrow.obj (comparisonArrow f) ≅ Arrow.mk f :=
  DerivedCategory.Qh.mapArrow.objObjPreimageIso (Arrow.mk f)

/-- The localization isomorphism of a specified quasi-isomorphism, with inverse given
by the formal reverse edge transported from the constructed localization model. -/
def homotopyFormalIso
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

/-- Invert the specified representative by a formal reverse edge in the localization
quiver, then transport along its proved arrow presentation. Only membership of this
actual representative in the quasi-isomorphisms is required. -/
def comparisonFormalIso {X Y : DerivedCategory (ModuleCat.{u} R)} (f : X ⟶ Y)
    (hf : HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)
      (comparisonArrow f).hom) : X ≅ Y :=
  (Arrow.leftFunc.mapIso (comparisonArrowIso f)).symm ≪≫
    homotopyFormalIso (comparisonArrow f).hom hf ≪≫
    Arrow.rightFunc.mapIso (comparisonArrowIso f)

/-- The formal construction retains the original comparison map exactly. -/
theorem comparisonFormalIso_hom {X Y : DerivedCategory (ModuleCat.{u} R)} (f : X ⟶ Y)
    (hf : HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)
      (comparisonArrow f).hom) : (comparisonFormalIso f hf).hom = f := by
  exact (Arrow.iso_w (comparisonArrowIso f)).symm

/-- Coproducts along total-complex antidiagonals exist in `ModuleCat R`. -/
instance hasTotal_moduleCat_bicomplex
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) :
    K.HasTotal (ComplexShape.up ℤ) :=
  sorry

/-- The total-complex functor on bicomplexes of `R`-modules commutes with the outer shift. -/
instance totalFunctor_commShift :
    (HomologicalComplex₂.totalFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).CommShift ℤ where
  commShiftIso n :=
    NatIso.ofComponents
      (fun K => HomologicalComplex₂.totalShift₁Iso (x := n) (K := K))
      (fun _ => sorry)
  commShiftIso_zero := sorry
  commShiftIso_add _ _ := sorry

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
include A B

/-- Degreewise extension of scalars along `P_n → B` is additive. -/
instance extensionDegreewise_additive :
    (extensionDegreewise A B).Additive :=
  sorry

/-- Degreewise extension of scalars admits an unbounded left derived functor. -/
instance extensionDegreewise_hasLeftDerived :
    (Functor.Homotopy.toDerived (extensionDegreewise A B)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (PresheafOfModules.{u} (standardSimplicialRing A B)) (ComplexShape.up ℤ)) :=
  sorry

/-- Degreewise extension of scalars admits a pointwise left derived functor. -/
instance extensionDegreewise_hasPointwiseLeftDerived :
    (Functor.Homotopy.toDerived (extensionDegreewise A B)).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (PresheafOfModules.{u} (standardSimplicialRing A B)) (ComplexShape.up ℤ)) :=
  sorry

/-- Derived extension of scalars along `P_• ⟶ B`. -/
def derivedExtension :
    DerivedCategory (PresheafOfModules.{u} (standardSimplicialRing A B)) ⥤
      DerivedCategory (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) :=
  Functor.LeftDerived.Homotopy.functor (extensionDegreewise A B)

/-- Derived extension of scalars commutes with integer shifts. -/
instance derivedExtension_commShift :
    (derivedExtension A B).CommShift ℤ :=
  Functor.totalLeftDerived_commShift
    (Functor.Homotopy.toDerived (extensionDegreewise A B))
    (HomotopyCategory.quasiIso
      (PresheafOfModules.{u} (standardSimplicialRing A B)) (ComplexShape.up ℤ))
    (DerivedCategory.Qh :
      HomotopyCategory (PresheafOfModules.{u} (standardSimplicialRing A B))
        (ComplexShape.up ℤ) ⥤
        DerivedCategory (PresheafOfModules.{u} (standardSimplicialRing A B)))

/-- The Moore cochain complex of a simplicial `B`-module. -/
def mooreExtend :
    (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) ⥤ CochainComplex (ModuleCat.{u} B) ℤ :=
  let _u := under A B
  alternatingFaceMapComplex (ModuleCat.{u} B) ⋙
    ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} B)

/-- Moore evaluation is additive. -/
instance mooreExtend_additive : (mooreExtend A B).Additive :=
  sorry

/-- Unfolding of `mooreExtend` as alternating faces followed by the integer embedding. -/
theorem mooreExtend_obj (N : SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) :
    (mooreExtend A B).obj N =
      ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj N).extend
        ComplexShape.embeddingDownNat :=
  sorry

/-- The total-complex shape sends `(0, n)` to `n`. -/
theorem π_up_zero (n : ℤ) :
    ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (0, n) = n :=
  sorry

/-- Inclusion of the degree-zero row into the total complex of a single bicomplex. -/
def totalSingleι (K : CochainComplex (ModuleCat.{u} B) ℤ) (n : ℤ) :
    K.X n ⟶
      (HomologicalComplex₂.total
        ((HomologicalComplex.single (CochainComplex (ModuleCat.{u} B) ℤ)
            (ComplexShape.up ℤ) 0).obj K)
        (ComplexShape.up ℤ)).X n :=
  let _u := under A B
  HomologicalComplex₂.ιTotal
    ((HomologicalComplex.single (CochainComplex (ModuleCat.{u} B) ℤ)
        (ComplexShape.up ℤ) 0).obj K)
    (ComplexShape.up ℤ) 0 n n (π_up_zero A B n)

/-- The degree-zero row inclusion `totalSingleι` is invertible. -/
instance totalSingleι_isIso (K : CochainComplex (ModuleCat.{u} B) ℤ) (n : ℤ) :
    IsIso (totalSingleι A B K n) :=
  sorry

/-- Totalization of a degree-zero single bicomplex recovers the original complex. -/
def totalSingleIso (K : CochainComplex (ModuleCat.{u} B) ℤ) :
    HomologicalComplex₂.total
        ((HomologicalComplex.single (CochainComplex (ModuleCat.{u} B) ℤ)
            (ComplexShape.up ℤ) 0).obj K)
        (ComplexShape.up ℤ) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (asIso (totalSingleι A B K n)).symm)
    (fun _ _ _ => sorry)

/-- Degreewise Moore evaluation of a complex of simplicial `B`-modules, then totalization. -/
def evaluationOnComplex :
    CochainComplex (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) ℤ ⥤
      DerivedCategory (ModuleCat.{u} B) :=
  (mooreExtend A B).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex₂.totalFunctor (ModuleCat.{u} B) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q

/-- Moore totalization inverts quasi-isomorphisms of complexes of simplicial modules. -/
theorem evaluationOnComplex_inverts :
    (HomologicalComplex.quasiIso (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B)
        (ComplexShape.up ℤ)).IsInvertedBy
      (evaluationOnComplex A B) :=
  sorry

/-- Lemma 92.4.1 evaluation of a simplicial `B`-module, as Moore totalization on `D`. -/
def evaluation :
    DerivedCategory (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) ⥤
      DerivedCategory (ModuleCat.{u} B) :=
  let _u := under A B
  CategoryTheory.Localization.lift
    (evaluationOnComplex A B) (evaluationOnComplex_inverts A B)
    (DerivedCategory.Q :
      CochainComplex (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) ℤ ⥤
        DerivedCategory (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B))

/-- Moore totalization of a complex of simplicial modules commutes with integer shifts. -/
instance evaluationOnComplex_commShift :
    (evaluationOnComplex A B).CommShift ℤ :=
  inferInstanceAs
    (((mooreExtend A B).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex₂.totalFunctor (ModuleCat.{u} B) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q).CommShift ℤ)

/-- Lemma 92.4.1 evaluation is the localization lift of Moore totalization. -/
instance evaluation_lifting :
    Localization.Lifting
      (DerivedCategory.Q :
        CochainComplex (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) ℤ ⥤
          DerivedCategory (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B))
      (HomologicalComplex.quasiIso (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B)
        (ComplexShape.up ℤ))
      (evaluationOnComplex A B) (evaluation A B) :=
  Localization.liftingLift (evaluationOnComplex A B) (evaluationOnComplex_inverts A B)
    (DerivedCategory.Q :
      CochainComplex (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) ℤ ⥤
        DerivedCategory (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B))

/-- Lemma 92.4.1 evaluation commutes with integer shifts. -/
instance evaluation_commShift :
    (evaluation A B).CommShift ℤ :=
  Functor.commShiftOfLocalization
    (DerivedCategory.Q :
      CochainComplex (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) ℤ ⥤
        DerivedCategory (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B))
    (HomologicalComplex.quasiIso (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B)
      (ComplexShape.up ℤ))
    ℤ (evaluationOnComplex A B) (evaluation A B)

/-- Comparison `L(colim)(single N) ≅ Q(Moore N)` realized as Moore totalization of a single. -/
def evaluationSingleIso (N : SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) :
    (evaluation A B).obj
        ((DerivedCategory.singleFunctor
            (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) 0).obj N) ≅
      DerivedCategory.Q.obj ((mooreExtend A B).obj N) :=
  (evaluation A B).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ
          (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) 0).app N) ≪≫
    (CategoryTheory.Localization.fac (evaluationOnComplex A B)
        (evaluationOnComplex_inverts A B)
        (DerivedCategory.Q :
          CochainComplex (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) ℤ ⥤
            DerivedCategory (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B))).app
      ((HomologicalComplex.single (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B)
          (ComplexShape.up ℤ) 0).obj N) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex₂.totalFunctor (ModuleCat.{u} B) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex (mooreExtend A B)
            (ComplexShape.up ℤ) 0).app N)) ≪≫
    DerivedCategory.Q.mapIso (totalSingleIso A B ((mooreExtend A B).obj N))

/-- Derived lower shriek `Lπ_!` of a simplicial `P_•`-module: derived tensor along
`P_n → B`, then Lemma 92.4.1 evaluation. -/
def lowerShriek :
    DerivedCategory (PresheafOfModules.{u} (standardSimplicialRing A B)) ⥤
      DerivedCategory (ModuleCat.{u} B) :=
  derivedExtension A B ⋙ evaluation A B

/-- Derived lower shriek commutes with integer shifts. -/
instance lowerShriek_commShift : (lowerShriek A B).CommShift ℤ :=
  inferInstanceAs ((derivedExtension A B ⋙ evaluation A B).CommShift ℤ)

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
      (extensionDegreewise A B).obj (cotangentModule A B M) where
  app n :=
    -- Local instance justification (noncanonical choice): the algebra structure on B over
    -- each standard-resolution term is the augmentation P_n → B, which depends on n.
    letI : Algebra (standardTerm A B n).right B := (augmentationHom A B n).toAlgebra
    ((ModuleCat.extendScalars (augmentationHom A B n)).obj
        (CommRingCat.KaehlerDifferential (standardTerm A B n).hom) ◁
      ModuleCat.ofHom
        { toFun := fun m : M =>
            (1 : B) ⊗ₜ[standardTerm A B n |>.right] m
          map_add' := sorry
          map_smul' := sorry }) ≫
      (Functor.Monoidal.μIso (ModuleCat.extendScalars (augmentationHom A B n))
          (CommRingCat.KaehlerDifferential (standardTerm A B n).hom)
          (restrictModule A B M n)).hom
  naturality := fun {X Y} f => sorry

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

/-- The underived tensor-associativity comparison is invertible. This does not assert
flatness of `Ω_{P_n/A} ⊗ M` or invertibility of the derived-extension counit. -/
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
      (extensionDegreewise A B).obj (restrictedModule A B M) where
  app n :=
    -- Local instance justification (noncanonical choice): the algebra structure on B over
    -- each standard-resolution term is the augmentation P_n → B, which depends on n.
    letI : Algebra (standardTerm A B n).right B := (augmentationHom A B n).toAlgebra
    ModuleCat.ofHom
      { toFun := fun m : M => (1 : B) ⊗ₜ[standardTerm A B n |>.right] m
        map_add' := sorry
        map_smul' := sorry }
  naturality := fun {X Y} f => sorry

/-- Lemma 92.4.4: the evaluation complex of `underline{M}` is identified with the degree-zero
single complex of `M`. -/
def constantIsoSingle (M : ModuleCat.{u} B) :
    DerivedCategory.Q.obj (constantComplex A B M) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M where
  hom := DerivedCategory.Q.map (constantToSingle A B M)
  inv := DerivedCategory.Q.map (singleToConstant A B M)
  hom_inv_id := sorry
  inv_hom_id := sorry

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

/-- The summand inclusion of `cotangentComplex.X n ⊗ M` into the tensor with the
degree-zero single of `M` is invertible. -/
instance ιTensorObj_cotangent_single_isIso (M : ModuleCat.{u} B) (n : ℤ) :
    IsIso (HomologicalComplex.ιTensorObj (Algebra.cotangentComplex A B)
      ((HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj M) n 0 n
      (add_zero n)) :=
  sorry

/-- If `n` is non-positive, then `n = -n.natAbs`. -/
theorem eq_neg_natAbs_of_not_pos {n : ℤ} (hn : ¬ 0 < n) : n = -n.natAbs :=
  sorry

/-- The total-complex shape sends `(-n.natAbs, 0)` to `n` when `n = -n.natAbs`. -/
theorem π_up_neg_natAbs (n : ℤ) (hn : n = -n.natAbs) :
    ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (-(n.natAbs : ℤ), 0) = n :=
  sorry

/-- The summand inclusion of `cotangentComplex.X (-n.natAbs) ⊗ M` into the tensor with the
degree-zero single of `M`. -/
def ιTensorCotangentSingle (M : ModuleCat.{u} B) (n : ℤ) (hn : n = -n.natAbs) :
    ((Algebra.cotangentComplex A B).X (-(n.natAbs : ℤ)) ⊗
      ((HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj M).X 0) ⟶
      (Algebra.cotangentComplex A B ⊗
        (HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj M).X n :=
  HomologicalComplex.ιTensorObj (Algebra.cotangentComplex A B)
    ((HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj M)
    (-(n.natAbs : ℤ)) 0 n (π_up_neg_natAbs A B n hn)

/-- The summand inclusion `ιTensorCotangentSingle` is invertible. -/
instance ιTensorCotangentSingle_isIso (M : ModuleCat.{u} B) (n : ℤ)
    (hn : n = -n.natAbs) :
    IsIso (ιTensorCotangentSingle A B M n hn) :=
  sorry

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
      have hn' : n = -n.natAbs := eq_neg_natAbs_of_not_pos A B hn
      HomologicalComplex.XIsoOfEq (tensorCochain A B M) hn' ≪≫
      tensorCochain_X A B M n.natAbs ≪≫
      (MonoidalCategory.tensorRight M).mapIso
        (CommRingCat.Under.CotangentComplex.objXIso (CommRingCat.of A)
          (under A B) n.natAbs).symm ≪≫
      (whiskerLeftIso ((Algebra.cotangentComplex A B).X (-(n.natAbs : ℤ)))
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).symm) ≪≫
      asIso (ιTensorCotangentSingle A B M n hn'))

/-- Cochain-level identification `tensorCochain ≅ cotangentComplex ⊗ single M`. -/
def tensorCochainIsoTensorSingle (M : ModuleCat.{u} B) :
    tensorCochain A B M ≅
      Algebra.cotangentComplex A B ⊗
        (HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj M :=
  HomologicalComplex.Hom.isoOfComponents (tensorCochainXIsoTensorSingle A B M)
    (fun _ _ _ => sorry)

/-- The two-variable derived-tensor counit at the standard cotangent complex against `M`
is invertible by flatness of the polynomial-resolution terms. -/
instance counitAppOfQ_cotangent_single_isIso (M : ModuleCat.{u} B) :
    IsIso (DerivedCategory.DerivedTensor.Bifunctor.counitAppOfQ
      (Algebra.cotangentComplex A B)
      ((HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj M)) :=
  sorry

/-- The comparison `L_{B/A} ⊗_B M ≅ L_{B/A} ⊗^L_B M` using flatness of the standard terms. -/
def tensorModule_iso_derived (M : ModuleCat.{u} B) :
    tensorModule A B M ≅
      (DerivedCategory.derivedTensorProduct
          ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M)).obj
        (DerivedCategory.Q.obj (Algebra.cotangentComplex A B)) :=
  DerivedCategory.Q.mapIso (tensorCochainIsoTensorSingle A B M) ≪≫
    (asIso (DerivedCategory.DerivedTensor.Bifunctor.counitAppOfQ
        (Algebra.cotangentComplex A B)
        ((HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj M))).symm ≪≫
    (DerivedCategory.DerivedTensor.Bifunctor.leftFunctor
        (DerivedCategory.Q.obj (Algebra.cotangentComplex A B))).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} B) 0).app M).symm ≪≫
    (DerivedCategory.DerivedTensorProduct.objIsoBifunctor
        (DerivedCategory.Q.obj (Algebra.cotangentComplex A B))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M)).symm

/-- The derived-extension counit on `Ω ⊗ M` becomes invertible after Moore totalization.
The source route is Cohomology on Sites, `lemma-O-homology-qis` and Remark 09CZ,
applied to the standard-resolution augmentation, together with 08PT. The cotangent
tensor has a compatible `B`-module structure. This is a totalized comparison; it does
not assert degreewise flatness of `Ω ⊗ M`. The comparison proof remains Prop debt. -/
theorem cotangentComparison_quasiIso (M : ModuleCat.{u} B) :
    HomotopyCategory.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)
      (comparisonArrow ((evaluation A B).map
        (derivedExtensionSingle A B (cotangentModule A B M)))).hom :=
  sorry

/-- Invertibility follows from the formal localization construction, not an assumed
existence of an inverse to the evaluated counit. -/
instance derivedExtensionSingle_cotangentModule_evaluation_isIso (M : ModuleCat.{u} B) :
    IsIso ((evaluation A B).map (derivedExtensionSingle A B (cotangentModule A B M))) := by
  simpa only [comparisonFormalIso_hom] using
    (comparisonFormalIso _ (cotangentComparison_quasiIso A B M)).isIso_hom

/-- Formal localization inverse of the specified post-evaluation comparison on `Ω ⊗ M`.
This is an arrow-representative construction, not a claimed cycle-level lift. -/
def derivedExtensionSingle_cotangentModule_evaluation_inv (M : ModuleCat.{u} B) :
    (evaluation A B).obj
        ((DerivedCategory.singleFunctor
            (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) 0).obj
          ((extensionDegreewise A B).obj (cotangentModule A B M))) ⟶
      (evaluation A B).obj
        ((derivedExtension A B).obj
          ((DerivedCategory.singleFunctor
              (PresheafOfModules.{u} (standardSimplicialRing A B)) 0).obj
            (cotangentModule A B M))) :=
  (comparisonFormalIso _ (cotangentComparison_quasiIso A B M)).inv

/-- The derived-extension counit on the restricted constant module becomes invertible
after Moore totalization. The source route uses `lemma-O-homology-qis` and Remark 09CZ
for the standard-resolution augmentation, followed by 08QE. The comparison proof
remains Prop debt; no degreewise acyclicity of the restricted module is asserted. -/
theorem restrictedComparison_quasiIso (M : ModuleCat.{u} B) :
    HomotopyCategory.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)
      (comparisonArrow ((evaluation A B).map
        (derivedExtensionSingle A B (restrictedModule A B M)))).hom :=
  sorry

/-- Invertibility of the constant-module comparison follows from its formal inverse. -/
instance derivedExtensionSingle_restrictedModule_evaluation_isIso (M : ModuleCat.{u} B) :
    IsIso ((evaluation A B).map (derivedExtensionSingle A B (restrictedModule A B M))) := by
  simpa only [comparisonFormalIso_hom] using
    (comparisonFormalIso _ (restrictedComparison_quasiIso A B M)).isIso_hom

/-- Formal localization inverse of the specified constant-module comparison.
The underived `m ↦ 1 ⊗ m` is not used as a substitute for a derived lift. -/
def derivedExtensionSingle_restrictedModule_evaluation_inv (M : ModuleCat.{u} B) :
    (evaluation A B).obj
        ((DerivedCategory.singleFunctor
            (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) 0).obj
          ((extensionDegreewise A B).obj (restrictedModule A B M))) ⟶
      (evaluation A B).obj
        ((derivedExtension A B).obj
          ((DerivedCategory.singleFunctor
              (PresheafOfModules.{u} (standardSimplicialRing A B)) 0).obj
            (restrictedModule A B M))) :=
  (comparisonFormalIso _ (restrictedComparison_quasiIso A B M)).inv

/-- The cotangent formal inverse is a right inverse to the original evaluated counit. -/
theorem cotangentComparison_hom_inv_id (M : ModuleCat.{u} B) :
    (evaluation A B).map (derivedExtensionSingle A B (cotangentModule A B M)) ≫
      derivedExtensionSingle_cotangentModule_evaluation_inv A B M = 𝟙 _ := by
  simpa only [comparisonFormalIso_hom,
    derivedExtensionSingle_cotangentModule_evaluation_inv] using
    (comparisonFormalIso _ (cotangentComparison_quasiIso A B M)).hom_inv_id

/-- The cotangent formal inverse is a left inverse to the original evaluated counit. -/
theorem cotangentComparison_inv_hom_id (M : ModuleCat.{u} B) :
    derivedExtensionSingle_cotangentModule_evaluation_inv A B M ≫
      (evaluation A B).map (derivedExtensionSingle A B (cotangentModule A B M)) = 𝟙 _ := by
  simpa only [comparisonFormalIso_hom,
    derivedExtensionSingle_cotangentModule_evaluation_inv] using
    (comparisonFormalIso _ (cotangentComparison_quasiIso A B M)).inv_hom_id

/-- The constant-module formal inverse is a right inverse to the specified comparison. -/
theorem restrictedComparison_hom_inv_id (M : ModuleCat.{u} B) :
    (evaluation A B).map (derivedExtensionSingle A B (restrictedModule A B M)) ≫
      derivedExtensionSingle_restrictedModule_evaluation_inv A B M = 𝟙 _ := by
  simpa only [comparisonFormalIso_hom,
    derivedExtensionSingle_restrictedModule_evaluation_inv] using
    (comparisonFormalIso _ (restrictedComparison_quasiIso A B M)).hom_inv_id

/-- The constant-module formal inverse is a left inverse to the specified comparison. -/
theorem restrictedComparison_inv_hom_id (M : ModuleCat.{u} B) :
    derivedExtensionSingle_restrictedModule_evaluation_inv A B M ≫
      (evaluation A B).map (derivedExtensionSingle A B (restrictedModule A B M)) = 𝟙 _ := by
  simpa only [comparisonFormalIso_hom,
    derivedExtensionSingle_restrictedModule_evaluation_inv] using
    (comparisonFormalIso _ (restrictedComparison_quasiIso A B M)).inv_hom_id

/-- The comparison isomorphism `Lπ_!(Ω_{P_•/A} ⊗ M) ≅ L_{B/A} ⊗_B M` after Lemma 92.4.1
evaluation, using the underived comparison `B ⊗_{P_n} (Ω ⊗_{P_n} M) ≅ (Ω ⊗_{P_n} B) ⊗_B M`. -/
def tensorIso (M : ModuleCat.{u} B) :
    (triangleOfSES A B M).obj₁ ≅ tensorModule A B M where
  hom :=
    (evaluation A B).map (derivedExtensionSingle A B (cotangentModule A B M)) ≫
      (evaluation A B).map
        ((DerivedCategory.singleFunctor
            (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) 0).map
          (cotangentExtend A B M)) ≫
      (evaluationSingleIso A B (simplicialCotangent A B M)).hom
  inv :=
    (evaluationSingleIso A B (simplicialCotangent A B M)).inv ≫
      (evaluation A B).map
        ((DerivedCategory.singleFunctor
            (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) 0).map
          (cotangentExtendInv A B M)) ≫
      derivedExtensionSingle_cotangentModule_evaluation_inv A B M
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The comparison isomorphism `Lπ_!(restricted M) ≅ M` via the cycle-level unit `m ↦ 1 ⊗ m`
into the underived extension and the 08QE identification after evaluation. -/
def moduleIso (M : ModuleCat.{u} B) :
    (triangleOfSES A B M).obj₃ ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M where
  hom :=
    (evaluation A B).map (derivedExtensionSingle A B (restrictedModule A B M)) ≫
      (evaluation A B).map
        ((DerivedCategory.singleFunctor
            (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) 0).map
          (restrictedExtendCounit A B M)) ≫
      (evaluationSingleIso A B (simplicialConstant A B M)).hom ≫
      (constantIsoSingle A B M).hom
  inv :=
    (constantIsoSingle A B M).inv ≫
      (evaluationSingleIso A B (simplicialConstant A B M)).inv ≫
      (evaluation A B).map
        ((DerivedCategory.singleFunctor
            (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) 0).map
          (restrictedExtendUnit A B M)) ≫
      derivedExtensionSingle_restrictedModule_evaluation_inv A B M
  hom_inv_id := sorry
  inv_hom_id := sorry

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
