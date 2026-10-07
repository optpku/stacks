module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.TotalComplexShift
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Shift.Localization
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Pullback.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Zero
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings.Triangulated
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Bifunctor
public import ReasLib.AlgebraicTopology.SimplicialObject.Augmentation
public import stacks_project.Chap92.«92_19_0_2_PrincipalParts»

/-!
# Atiyah triangle of a sheaf of modules

Applying the augmentation lower shriek `Lπ_! : D(P_•) ⟶ D(B)` of the standard-resolution
augmentation `P_• ⟶ B` to the simplicial first principal-parts sequence produces a distinguished
triangle in `D(B)`, displayed on the vertices `L(φ) ⊗^L F`, `Lπ_!(P¹_{P_•/A}(F))`, and `F`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open ComplexShape
open Opposite
open HomologicalComplex
open AlgebraicTopology
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.CotangentComplex
open scoped Simplicial
open scoped SheafOfModules.RingedSite.CotangentComplex
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace SheafOfModules.RingedSite.CotangentComplex

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
variable [UnivLE.{u, u}]
variable [HasSheafify (SimplicialSite.topology J) AddCommGrpCat.{u}]
variable [GrothendieckTopology.WEqualsLocallyBijective
    (SimplicialSite.topology J) AddCommGrpCat.{u}]
variable [GrothendieckTopology.HasSheafCompose (SimplicialSite.topology J)
    (forget₂ CommRingCat.{u} RingCat.{u})]
variable {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
variable (F : ringedSiteModuleCategory J B)

-- Local instance justification (defeq pin): `moduleCategoryHasDerivedCategory` and
-- `moduleCategoryAbelian` are the reducible standard owners for ringed-site modules;
-- simplicial-site modules are that same category, and `singleTriangle`/`mapTriangle`
-- need them without registering a second derived-category instance.
attribute [local instance] moduleCategoryHasDerivedCategory
attribute [local instance] moduleCategoryAbelian

variable [DerivedCategory.DerivedTensor.Has (C := ringedSiteModuleCategory J B)]
variable [DerivedCategory.DerivedTensor.Left.Has (C := ringedSiteModuleCategory J B)]
variable [DerivedCategory.DerivedTensor.Bifunctor.Has (C := ringedSiteModuleCategory J B)]

/-- The standard derived-category instance on simplicial diagrams of ringed-site modules. -/
instance simplicialDiagramHasDerivedCategory :
    HasDerivedCategory (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B) :=
  HasDerivedCategory.standard _

/-- A representative of the specified derived comparison in the homotopy arrow category.
Its existence is Mathlib's proved essential surjectivity of `Qh.mapArrow`, independent
of any assertion that the specified comparison is invertible. -/
def comparisonArrow {X Y : DerivedCategory (ringedSiteModuleCategory J B)} (f : X ⟶ Y) :
    Arrow (HomotopyCategory (ringedSiteModuleCategory J B) (ComplexShape.up ℤ)) :=
  DerivedCategory.Qh.mapArrow.objPreimage (Arrow.mk f)

/-- The chosen representative presents the original arrow, including its endpoints
and its commutative square; it is not an arbitrary isomorphism of the endpoints. -/
def comparisonArrowIso {X Y : DerivedCategory (ringedSiteModuleCategory J B)} (f : X ⟶ Y) :
    DerivedCategory.Qh.mapArrow.obj (comparisonArrow f) ≅ Arrow.mk f :=
  DerivedCategory.Qh.mapArrow.objObjPreimageIso (Arrow.mk f)

/-- The localization isomorphism of a specified quasi-isomorphism, with inverse given
by the formal reverse edge transported from the constructed localization model. -/
def homotopyFormalIso
    {K L : HomotopyCategory (ringedSiteModuleCategory J B) (ComplexShape.up ℤ)} (f : K ⟶ L)
    (hf : HomotopyCategory.quasiIso (ringedSiteModuleCategory J B) (ComplexShape.up ℤ) f) :
    DerivedCategory.Qh.obj K ≅ DerivedCategory.Qh.obj L where
  hom := DerivedCategory.Qh.map f
  inv := Localization.homEquiv
    (HomotopyCategory.quasiIso (ringedSiteModuleCategory J B) (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso (ringedSiteModuleCategory J B) (ComplexShape.up ℤ)).Q
    DerivedCategory.Qh (Localization.Construction.wInv f hf)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Invert the specified representative by a formal reverse edge in the localization
quiver, then transport along its proved arrow presentation. Only membership of this
actual representative in the quasi-isomorphisms is required. -/
def comparisonFormalIso {X Y : DerivedCategory (ringedSiteModuleCategory J B)} (f : X ⟶ Y)
    (hf : HomotopyCategory.quasiIso (ringedSiteModuleCategory J B) (ComplexShape.up ℤ)
      (comparisonArrow f).hom) : X ≅ Y :=
  (Arrow.leftFunc.mapIso (comparisonArrowIso f)).symm ≪≫
    homotopyFormalIso (comparisonArrow f).hom hf ≪≫
    Arrow.rightFunc.mapIso (comparisonArrowIso f)

/-- The formal construction retains the original comparison map exactly. -/
theorem comparisonFormalIso_hom {X Y : DerivedCategory (ringedSiteModuleCategory J B)} (f : X ⟶ Y)
    (hf : HomotopyCategory.quasiIso (ringedSiteModuleCategory J B) (ComplexShape.up ℤ)
      (comparisonArrow f).hom) : (comparisonFormalIso f hf).hom = f :=
  sorry

/-- Coproducts along total-complex antidiagonals exist in ringed-site modules. -/
instance hasTotal_ringedSite_bicomplex
    (K : HomologicalComplex₂ (ringedSiteModuleCategory J B)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) :
    K.HasTotal (ComplexShape.up ℤ) :=
  sorry

/-- The total-complex functor on bicomplexes of ringed-site modules commutes with the outer
shift. -/
instance totalFunctor_commShift :
    (HomologicalComplex₂.totalFunctor (ringedSiteModuleCategory J B) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).CommShift ℤ where
  commShiftIso n :=
    NatIso.ofComponents
      (fun K => HomologicalComplex₂.totalShift₁Iso (x := n) (K := K))
      (fun _ => sorry)
  commShiftIso_zero := sorry
  commShiftIso_add _ _ := sorry

/-- The opposite product morphism keeping the simplicial degree fixed. -/
def degreeSliceHom (n : SimplexCategoryᵒᵖ) {U V : Cᵒᵖ} (f : U ⟶ V) :
    op (n.unop, U.unop) ⟶ op (n.unop, V.unop) :=
  Quiver.Hom.op (⟨𝟙 n.unop, f.unop⟩ : (n.unop, V.unop) ⟶ (n.unop, U.unop))

/-- The opposite product morphism keeping the site object fixed. -/
def simplexSliceHom {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (U : Cᵒᵖ) :
    op (n.unop, U.unop) ⟶ op (m.unop, U.unop) :=
  Quiver.Hom.op (⟨f.unop, 𝟙 U.unop⟩ : (m.unop, U.unop) ⟶ (n.unop, U.unop))

/-- The degree-`n` module sheaf on `C` obtained by evaluating a simplicial-site module. -/
def evalAtDegree {𝒪 : SimplicialObject (Sheaf J CommRingCat.{u})}
    (X : SimplicialSite.ModuleCat (J := J) 𝒪) (n : SimplexCategoryᵒᵖ) :
    ringedSiteModuleCategory J (𝒪.obj n) where
  val :=
    { obj := fun U ↦ X.val.obj (op (n.unop, U.unop))
      map := fun {U V} f ↦
        ModuleCat.homMk
          (AddCommGrpCat.ofHom
            (AddMonoidHom.mk'
              (fun t ↦ (X.val.map (degreeSliceHom (C := C) n f)).hom t)
              sorry))
          sorry
      map_id := sorry
      map_comp := sorry }
  isSheaf := sorry

/-- Unfolding of `evalAtDegree` on sections over `U`. -/
theorem evalAtDegree_obj {𝒪 : SimplicialObject (Sheaf J CommRingCat.{u})}
    (X : SimplicialSite.ModuleCat (J := J) 𝒪) (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) :
    (evalAtDegree X n).val.obj U = X.val.obj (op (n.unop, U.unop)) :=
  sorry

/-- The morphism on degree-`n` evaluations induced by a morphism of simplicial-site modules. -/
def evalAtDegreeHom {𝒪 : SimplicialObject (Sheaf J CommRingCat.{u})}
    {X Y : SimplicialSite.ModuleCat (J := J) 𝒪} (α : X ⟶ Y) (n : SimplexCategoryᵒᵖ) :
    evalAtDegree X n ⟶ evalAtDegree Y n where
  val :=
    { app := fun U ↦ α.val.app (op (n.unop, U.unop))
      naturality := sorry }

/-- A simplicial operator as a map of degreewise evaluations, after restriction of scalars. -/
def evalAtDegreeMap {𝒪 : SimplicialObject (Sheaf J CommRingCat.{u})}
    (X : SimplicialSite.ModuleCat (J := J) 𝒪) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    evalAtDegree X n ⟶ (restrictionAlong (𝒪.map f)).obj (evalAtDegree X m) where
  val :=
    { app := fun U ↦
        ModuleCat.homMk
          (AddCommGrpCat.ofHom
            (AddMonoidHom.mk'
              (fun t ↦ (X.val.map (simplexSliceHom (C := C) f U)).hom t)
              sorry))
          sorry
      naturality := sorry }

/-- Degreewise underived extension of scalars along the augmentations `P_n → B`. -/
def extensionMap (X : SimplicialSite.ModuleCat (J := J) (standardSimplicial φ))
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (extendAlong ((augmentation φ).app n)).obj (evalAtDegree X n) ⟶
      (extendAlong ((augmentation φ).app m)).obj (evalAtDegree X m) :=
  ((extendRestrictAdj ((augmentation φ).app n)).homEquiv _ _).symm
    (evalAtDegreeMap X f ≫
      (restrictionAlong ((standardSimplicial φ).map f)).map
        ((extendRestrictAdj ((augmentation φ).app m)).unit.app (evalAtDegree X m)) ≫
      (SheafOfModules.Restriction.compIso'
          (ringSheafMap ((standardSimplicial φ).map f))
          (ringSheafMap ((augmentation φ).app m))
          (ringSheafMap ((augmentation φ).app n))
          (standardSimplicial_map_comp_augmentation_ringSheaf φ f)).hom.app _)

/-- Degreewise underived extension of scalars along `P_• ⟶ B`, as a functor on simplicial
`P_•`-modules. -/
def extensionDegreewise :
    SimplicialSite.ModuleCat (J := J) (standardSimplicial φ) ⥤
      (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B) where
  obj X :=
    { obj := fun n ↦ (extendAlong ((augmentation φ).app n)).obj (evalAtDegree X n)
      map := fun {n m} f ↦ extensionMap φ X f
      map_id := sorry
      map_comp := sorry }
  map {X Y} α :=
    { app := fun n ↦ (extendAlong ((augmentation φ).app n)).map (evalAtDegreeHom α n)
      naturality := sorry }
  map_id := sorry
  map_comp := sorry

/-- Unfolding of `extensionDegreewise` on objects: degreewise `extendAlong` of `evalAtDegree`. -/
theorem extensionDegreewise_obj_obj
    (X : SimplicialSite.ModuleCat (J := J) (standardSimplicial φ)) (n : SimplexCategoryᵒᵖ) :
    ((extensionDegreewise φ).obj X).obj n =
      (extendAlong ((augmentation φ).app n)).obj (evalAtDegree X n) :=
  sorry

/-- Degreewise extension of scalars is additive. -/
instance extensionDegreewise_additive : (extensionDegreewise φ).Additive :=
  sorry

/-- Degreewise extension of scalars admits an unbounded left derived functor. -/
instance extensionDegreewise_hasLeftDerived :
    (Functor.Homotopy.toDerived (extensionDegreewise φ)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ))
        (ComplexShape.up ℤ)) :=
  sorry

/-- Degreewise extension of scalars admits a pointwise left derived functor. -/
instance extensionDegreewise_hasPointwiseLeftDerived :
    (Functor.Homotopy.toDerived (extensionDegreewise φ)).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ))
        (ComplexShape.up ℤ)) :=
  sorry

/-- Derived extension of scalars along `P_• ⟶ B`. -/
def derivedExtension :
    RingedSite.Hom.ModuleDerived
        (RingedSite.ofCommRingSheaf (SimplicialSite.topology J)
          (SimplicialSite.ringSheaf (standardSimplicial φ))) ⥤
      DerivedCategory (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B) :=
  Functor.LeftDerived.Homotopy.functor (extensionDegreewise φ)

/-- Derived extension of scalars commutes with integer shifts. -/
instance derivedExtension_commShift : (derivedExtension φ).CommShift ℤ :=
  Functor.totalLeftDerived_commShift
    (Functor.Homotopy.toDerived (extensionDegreewise φ))
    (HomotopyCategory.quasiIso
      (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ))
      (ComplexShape.up ℤ))
    (DerivedCategory.Qh :
      HomotopyCategory (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ))
        (ComplexShape.up ℤ) ⥤
        DerivedCategory (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ)))

/-- The Moore cochain complex of a simplicial `B`-module sheaf. -/
def mooreExtend :
    (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B) ⥤
      CochainComplex (ringedSiteModuleCategory J B) ℤ :=
  alternatingFaceMapComplex (ringedSiteModuleCategory J B) ⋙
    ComplexShape.embeddingDownNat.extendFunctor (ringedSiteModuleCategory J B)

/-- Moore evaluation is additive. -/
instance mooreExtend_additive : (mooreExtend (B := B)).Additive :=
  sorry

/-- The total-complex shape sends `(0, n)` to `n`. -/
theorem π_up_zero (n : ℤ) :
    ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (0, n) = n :=
  sorry

/-- Inclusion of the degree-zero row into the total complex of a single bicomplex. -/
def totalSingleι (K : CochainComplex (ringedSiteModuleCategory J B) ℤ) (n : ℤ) :
    K.X n ⟶
      (HomologicalComplex₂.total
        ((HomologicalComplex.single (CochainComplex (ringedSiteModuleCategory J B) ℤ)
            (ComplexShape.up ℤ) 0).obj K)
        (ComplexShape.up ℤ)).X n :=
  HomologicalComplex₂.ιTotal
    ((HomologicalComplex.single (CochainComplex (ringedSiteModuleCategory J B) ℤ)
        (ComplexShape.up ℤ) 0).obj K)
    (ComplexShape.up ℤ) 0 n n (π_up_zero n)

/-- The `(i₁, i₂)`-summand of a degree-zero single bicomplex in degree `n` identifies with
`K.X n` when `i₁ = 0`. -/
theorem totalSingle_component_eq (K : CochainComplex (ringedSiteModuleCategory J B) ℤ)
    (n i₁ i₂ : ℤ) (h : i₁ = 0)
    (hi : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (i₁, i₂) = n) :
    (((HomologicalComplex.single (CochainComplex (ringedSiteModuleCategory J B) ℤ)
        (ComplexShape.up ℤ) 0).obj K).X i₁).X i₂ =
      K.X n :=
  sorry

/-- Projection from the total complex of a degree-zero single bicomplex onto the original
complex in degree `n`. -/
def totalSingleπ (K : CochainComplex (ringedSiteModuleCategory J B) ℤ) (n : ℤ) :
    (HomologicalComplex₂.total
        ((HomologicalComplex.single (CochainComplex (ringedSiteModuleCategory J B) ℤ)
            (ComplexShape.up ℤ) 0).obj K)
        (ComplexShape.up ℤ)).X n ⟶ K.X n :=
  HomologicalComplex₂.totalDesc
    ((HomologicalComplex.single (CochainComplex (ringedSiteModuleCategory J B) ℤ)
        (ComplexShape.up ℤ) 0).obj K)
    (fun i₁ i₂ hi =>
      dite (i₁ = 0)
        (fun h => eqToHom (totalSingle_component_eq K n i₁ i₂ h hi))
        (fun _ => 0))

/-- Totalization of a degree-zero single bicomplex recovers the original complex. -/
def totalSingleIso (K : CochainComplex (ringedSiteModuleCategory J B) ℤ) :
    HomologicalComplex₂.total
        ((HomologicalComplex.single (CochainComplex (ringedSiteModuleCategory J B) ℤ)
            (ComplexShape.up ℤ) 0).obj K)
        (ComplexShape.up ℤ) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n =>
      { hom := totalSingleπ K n
        inv := totalSingleι K n
        hom_inv_id := sorry
        inv_hom_id := sorry })
    (fun _ _ _ => sorry)

/-- Degreewise Moore evaluation of a complex of simplicial `B`-modules, then totalization. -/
def evaluationOnComplex :
    CochainComplex (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B) ℤ ⥤
      DerivedCategory (ringedSiteModuleCategory J B) :=
  (mooreExtend (B := B)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex₂.totalFunctor (ringedSiteModuleCategory J B) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q

/-- Moore totalization inverts quasi-isomorphisms of complexes of simplicial modules. -/
theorem evaluationOnComplex_inverts :
    (HomologicalComplex.quasiIso (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B)
        (ComplexShape.up ℤ)).IsInvertedBy
      (evaluationOnComplex (B := B)) :=
  sorry

/-- Lemma 92.4.1 evaluation of a simplicial `B`-module sheaf, as Moore totalization on `D`. -/
def evaluation :
    DerivedCategory (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B) ⥤
      DerivedCategory (ringedSiteModuleCategory J B) :=
  CategoryTheory.Localization.lift
    (evaluationOnComplex (B := B)) (evaluationOnComplex_inverts (B := B))
    (DerivedCategory.Q :
      CochainComplex (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B) ℤ ⥤
        DerivedCategory (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B))

/-- Moore totalization of a complex of simplicial modules commutes with integer shifts. -/
instance evaluationOnComplex_commShift :
    (evaluationOnComplex (B := B)).CommShift ℤ :=
  inferInstanceAs
    (((mooreExtend (B := B)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex₂.totalFunctor (ringedSiteModuleCategory J B) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q).CommShift ℤ)

/-- Lemma 92.4.1 evaluation is the localization lift of Moore totalization. -/
instance evaluation_lifting :
    Localization.Lifting
      (DerivedCategory.Q :
        CochainComplex (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B) ℤ ⥤
          DerivedCategory (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B))
      (HomologicalComplex.quasiIso (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B)
        (ComplexShape.up ℤ))
      (evaluationOnComplex (B := B)) (evaluation (B := B)) :=
  Localization.liftingLift (evaluationOnComplex (B := B))
    (evaluationOnComplex_inverts (B := B))
    (DerivedCategory.Q :
      CochainComplex (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B) ℤ ⥤
        DerivedCategory (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B))

/-- Lemma 92.4.1 evaluation commutes with integer shifts. -/
instance evaluation_commShift : (evaluation (B := B)).CommShift ℤ :=
  Functor.commShiftOfLocalization
    (DerivedCategory.Q :
      CochainComplex (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B) ℤ ⥤
        DerivedCategory (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B))
    (HomologicalComplex.quasiIso (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B)
      (ComplexShape.up ℤ))
    ℤ (evaluationOnComplex (B := B)) (evaluation (B := B))

/-- Comparison `L(colim)(single N) ≅ Q(Moore N)` realized as Moore totalization of a single. -/
def evaluationSingleIso
    (N : SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B) :
    (evaluation (B := B)).obj
        ((DerivedCategory.singleFunctor
            (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B) 0).obj N) ≅
      DerivedCategory.Q.obj ((mooreExtend (B := B)).obj N) :=
  (evaluation (B := B)).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ
          (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B) 0).app N) ≪≫
    (CategoryTheory.Localization.fac (evaluationOnComplex (B := B))
        (evaluationOnComplex_inverts (B := B))
        (DerivedCategory.Q :
          CochainComplex (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B) ℤ ⥤
            DerivedCategory (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B))).app
      ((HomologicalComplex.single (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B)
          (ComplexShape.up ℤ) 0).obj N) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex₂.totalFunctor (ringedSiteModuleCategory J B) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex (mooreExtend (B := B))
            (ComplexShape.up ℤ) 0).app N)) ≪≫
    DerivedCategory.Q.mapIso (totalSingleIso ((mooreExtend (B := B)).obj N))

/-- Computational Moore-evaluation model of the augmentation lower shriek. -/
def computationalLowerShriek :
    RingedSite.Hom.ModuleDerived
        (RingedSite.ofCommRingSheaf (SimplicialSite.topology J)
          (SimplicialSite.ringSheaf (standardSimplicial φ))) ⥤
      RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J B) :=
  derivedExtension φ ⋙ evaluation (B := B)

/-- Unfolding of `computationalLowerShriek` as derived extension of scalars followed by Moore
evaluation. -/
theorem computationalLowerShriek_eq :
    computationalLowerShriek φ = derivedExtension φ ⋙ evaluation (B := B) :=
  sorry

/-- Forgetting rings and multiplication gives the additive sheaf used by the augmentation
complex. -/
abbrev additiveSheaf :
    Sheaf J CommRingCat.{u} ⥤ Sheaf J AddCommGrpCat.{u} :=
  sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u}) ⋙
    sheafCompose J (forget₂ RingCat.{u} AddCommGrpCat.{u})

/-- Unfolding of `additiveSheaf` as successive sheaf composition along the ring and additive
forgets. -/
theorem additiveSheaf_eq :
    additiveSheaf =
      sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u}) ⋙
        sheafCompose J (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  sorry

/-- A ring-valued augmentation regarded as an augmentation of additive sheaves. -/
abbrev additiveAugmentation
    {A : SimplicialObject (Sheaf J CommRingCat.{u})}
    {𝒪 : Sheaf J CommRingCat.{u}}
    (ε : A ⟶ (SimplicialObject.const (Sheaf J CommRingCat.{u})).obj 𝒪) :
    SimplicialObject.Augmented (Sheaf J AddCommGrpCat.{u}) :=
  (SimplicialObject.Augmented.whiskeringObj
      (Sheaf J CommRingCat.{u}) (Sheaf J AddCommGrpCat.{u}) additiveSheaf).obj
    (SimplicialObject.Augmentation.toAugmented ε)

/-- Unfolding of `additiveAugmentation` as whiskering of the bundled augmentation. -/
theorem additiveAugmentation_eq
    {A : SimplicialObject (Sheaf J CommRingCat.{u})}
    {𝒪 : Sheaf J CommRingCat.{u}}
    (ε : A ⟶ (SimplicialObject.const (Sheaf J CommRingCat.{u})).obj 𝒪) :
    additiveAugmentation ε =
      (SimplicialObject.Augmented.whiskeringObj
          (Sheaf J CommRingCat.{u}) (Sheaf J AddCommGrpCat.{u}) additiveSheaf).obj
        (SimplicialObject.Augmentation.toAugmented ε) :=
  sorry

/-- The alternating-face complex map induced by an augmentation. -/
abbrev augmentationComplexMap
    {A : SimplicialObject (Sheaf J CommRingCat.{u})}
    {𝒪 : Sheaf J CommRingCat.{u}}
    (ε : A ⟶ (SimplicialObject.const (Sheaf J CommRingCat.{u})).obj 𝒪) :=
  AlgebraicTopology.AlternatingFaceMapComplex.ε.app (additiveAugmentation ε)

/-- The standard-resolution augmentation `P_• ⟶ B` induces a quasi-isomorphism of
alternating-face complexes. -/
instance augmentation_quasiIso :
    QuasiIso (augmentationComplexMap (augmentation φ)) :=
  sorry

/-- Unfolding of `augmentationComplexMap` as the alternating-face augmentation of the
underlying additive simplicial sheaf. -/
theorem augmentationComplexMap_eq
    {A : SimplicialObject (Sheaf J CommRingCat.{u})}
    {𝒪 : Sheaf J CommRingCat.{u}}
    (ε : A ⟶ (SimplicialObject.const (Sheaf J CommRingCat.{u})).obj 𝒪) :
    augmentationComplexMap ε =
      AlgebraicTopology.AlternatingFaceMapComplex.ε.app (additiveAugmentation ε) :=
  sorry

/-- The derived lower shriek `Lπ_! : D(P_•) ⟶ D(B)` of the standard-resolution augmentation,
as the Moore-evaluation model obtained by derived extension of scalars along `P_• ⟶ B`
followed by Lemma 92.4.1 evaluation. -/
abbrev atiyahLowerShriek :
    RingedSite.Hom.ModuleDerived
        (RingedSite.ofCommRingSheaf (SimplicialSite.topology J)
          (SimplicialSite.ringSheaf (standardSimplicial φ))) ⥤
      RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J B) :=
  computationalLowerShriek φ

/-- Unfolding of `atiyahLowerShriek` as the Moore-evaluation model of `Lπ_!`. -/
theorem atiyahLowerShriek_eq :
    atiyahLowerShriek φ = computationalLowerShriek φ :=
  sorry

/-- Derived lower shriek commutes with integer shifts. -/
instance computationalLowerShriek_commShift : (computationalLowerShriek φ).CommShift ℤ :=
  inferInstanceAs ((derivedExtension φ ⋙ evaluation (B := B)).CommShift ℤ)

/-- The image of the simplicial first principal-parts sequence under the augmentation lower
shriek `Lπ_!` of `P_• ⟶ B`. -/
def atiyahTriangle_ofSES :
    Triangle (RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J B)) :=
  (atiyahLowerShriek φ).mapTriangle.obj
    (atiyahSequence_shortExact φ F).singleTriangle

/-- Unfolding of `atiyahTriangle_ofSES` as `Lπ_!` applied to the principal-parts
`singleTriangle`. -/
theorem atiyahTriangle_ofSES_eq :
    atiyahTriangle_ofSES φ F =
      (atiyahLowerShriek φ).mapTriangle.obj
        (atiyahSequence_shortExact φ F).singleTriangle :=
  sorry

/-- Comparison `L(extend)(single X) ⟶ single (extend X)` from the homotopy-to-derived counit. -/
def derivedExtensionSingle
    (X : SimplicialSite.ModuleCat (J := J) (standardSimplicial φ)) :
    (derivedExtension φ).obj
        ((DerivedCategory.singleFunctor
            (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ)) 0).obj X) ⟶
      (DerivedCategory.singleFunctor
          (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B) 0).obj
        ((extensionDegreewise φ).obj X) :=
  (Functor.LeftDerived.Homotopy.counit (extensionDegreewise φ)).app
      ((HomotopyCategory.singleFunctor
          (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ)) 0).obj X) ≫
    (Functor.Homotopy.singleIso (extensionDegreewise φ) 0).hom.app X

/-- After totalization, the cotangent counit has a quasi-isomorphism representative.
This uses the standard augmentation and the homology-augmentation comparison of 09D3;
it does not assert degreewise acyclicity of `Ω ⊗ F`. -/
theorem cotangentComparison_quasiIso :
    HomotopyCategory.quasiIso (ringedSiteModuleCategory J B) (ComplexShape.up ℤ)
      (comparisonArrow ((evaluation (B := B)).map
        (derivedExtensionSingle φ (cotangentModule φ F)))).hom :=
  sorry

/-- The totalized constant-module comparison is a quasi-isomorphism on its actual
homotopy representative. No arbitrary simplicial-site module is asserted acyclic. -/
theorem restrictedComparison_quasiIso :
    HomotopyCategory.quasiIso (ringedSiteModuleCategory J B) (ComplexShape.up ℤ)
      (comparisonArrow ((evaluation (B := B)).map
        (derivedExtensionSingle φ (restrictedModule φ F)))).hom :=
  sorry

/-- The evaluated cotangent counit is invertible. -/
instance derivedExtensionSingle_cotangent_isIso :
    IsIso ((evaluation (B := B)).map (derivedExtensionSingle φ (cotangentModule φ F))) :=
  sorry

/-- Inverse of the specified totalized cotangent comparison, as the formal localization
inverse of its homotopy representative. -/
def cotangentComparisonInv :=
  (comparisonFormalIso _
    (cotangentComparison_quasiIso φ F)).inv

/-- The evaluated constant-module counit is invertible. -/
instance derivedExtensionSingle_restricted_isIso :
    IsIso ((evaluation (B := B)).map (derivedExtensionSingle φ (restrictedModule φ F))) :=
  sorry

/-- Inverse of the specified totalized constant-module comparison, as the formal localization
inverse of its homotopy representative. -/
def restrictedComparisonInv :=
  (comparisonFormalIso _
    (restrictedComparison_quasiIso φ F)).inv

/-- The formal cotangent inverse is a right inverse to the actual evaluated counit. -/
theorem cotangentComparison_hom_inv_id :
    (evaluation (B := B)).map (derivedExtensionSingle φ (cotangentModule φ F)) ≫
      cotangentComparisonInv φ F = 𝟙 _ :=
  sorry

/-- The formal cotangent inverse is a left inverse to the actual evaluated counit. -/
theorem cotangentComparison_inv_hom_id :
    cotangentComparisonInv φ F ≫
      (evaluation (B := B)).map (derivedExtensionSingle φ (cotangentModule φ F)) = 𝟙 _ :=
  sorry

/-- The formal constant-module inverse is a right inverse to the specified comparison. -/
theorem restrictedComparison_hom_inv_id :
    (evaluation (B := B)).map (derivedExtensionSingle φ (restrictedModule φ F)) ≫
      restrictedComparisonInv φ F = 𝟙 _ :=
  sorry

/-- The formal constant-module inverse is a left inverse to the specified comparison. -/
theorem restrictedComparison_inv_hom_id :
    restrictedComparisonInv φ F ≫
      (evaluation (B := B)).map (derivedExtensionSingle φ (restrictedModule φ F)) = 𝟙 _ :=
  sorry

/-- The constant simplicial `B`-module with value `F`. -/
def simplicialConstant :
    SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B :=
  (Functor.const _).obj F

/-- Unfolding of `simplicialConstant`. -/
theorem simplicialConstant_obj (n : SimplexCategoryᵒᵖ) :
    (simplicialConstant F).obj n = F :=
  sorry

/-- The simplicial `B`-module `(Ω_{P_n/A} ⊗_{P_n} B) ⊗_B F`, the degreewise tensor of the
standard-resolution cotangent terms with `F`. -/
def simplicialCotangent :
    SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B where
  obj n := moduleTensor ((simplicialModule A (Under.mk φ)).obj n) F
  map f := moduleTensorMap ((simplicialModule A (Under.mk φ)).map f) (𝟙 F)
  map_id _ := sorry
  map_comp _ _ := sorry

/-- Degreewise, `simplicialCotangent` is the base change of `Ω_{P_n/A}` tensored with `F`. -/
theorem simplicialCotangent_obj (n : SimplexCategoryᵒᵖ) :
    (simplicialCotangent φ F).obj n =
      moduleTensor ((simplicialModule A (Under.mk φ)).obj n) F :=
  sorry

/-- The cochain complex of `B`-modules obtained from `simplicialCotangent`. -/
def tensorCochain : CochainComplex (ringedSiteModuleCategory J B) ℤ :=
  (mooreExtend (B := B)).obj (simplicialCotangent φ F)

/-- Unfolding of `tensorCochain` as Moore evaluation of `simplicialCotangent`. -/
theorem tensorCochain_eq :
    tensorCochain φ F = (mooreExtend (B := B)).obj (simplicialCotangent φ F) :=
  sorry

/-- Underlying additive identity of a module-sheaf section, as an `AddCommGrpCat` morphism. -/
def addCommId {𝒪 : Sheaf J CommRingCat.{u}} (M : ringedSiteModuleCategory J 𝒪) (U : Cᵒᵖ) :
    (forget₂ (ModuleCat _) AddCommGrpCat).obj (M.val.obj U) ⟶
      (forget₂ (ModuleCat _) AddCommGrpCat).obj (M.val.obj U) :=
  AddCommGrpCat.ofHom
    { toFun := fun t ↦ t
      map_zero' := sorry
      map_add' := sorry }

/-- Sectionwise identity from the degree-`n` evaluation of `restrictedModule` to the restricted
copy of `F`. -/
def evalAtDegreeToRestricted (n : SimplexCategoryᵒᵖ) :
    evalAtDegree (restrictedModule φ F) n ⟶
      (restrictionAlong ((augmentation φ).app n)).obj F where
  val :=
    { app := fun U ↦ ModuleCat.homMk (addCommId F U) sorry
      naturality := sorry }

/-- The counit `B ⊗_{P_n} F ⟶ F` of extension of scalars, as a simplicial map. -/
def restrictedExtendCounit :
    (extensionDegreewise φ).obj (restrictedModule φ F) ⟶ simplicialConstant F where
  app n :=
    ((extendRestrictAdj ((augmentation φ).app n)).homEquiv
        (evalAtDegree (restrictedModule φ F) n) F).symm
      (evalAtDegreeToRestricted φ F n)
  naturality := fun {X Y} f => sorry

/-- Degreewise `B ⊗_{P_n} F ⟶ F` is invertible on the restriction of a `B`-module. -/
instance restrictedExtendCounit_isIso : IsIso (restrictedExtendCounit φ F) :=
  sorry

/-- Sectionwise identity from the restricted copy of `F` to the degree-`n` evaluation of
`restrictedModule`. -/
def evalAtDegreeFromRestricted (n : SimplexCategoryᵒᵖ) :
    (restrictionAlong ((augmentation φ).app n)).obj F ⟶
      evalAtDegree (restrictedModule φ F) n where
  val :=
    { app := fun U ↦ ModuleCat.homMk (addCommId F U) sorry
      naturality := sorry }

/-- The canonical comparison `G ⟶ B ⊗_P G` sending a section `t` to `1 ⊗ t`, obtained by
rebundling the extension-restriction unit of the restricted module as a map of `B`-modules. -/
def extendRestrictUnit {𝒪 𝒪' : Sheaf J CommRingCat.{u}} (α : 𝒪 ⟶ 𝒪')
    (G : ringedSiteModuleCategory J 𝒪') :
    G ⟶ (extendAlong α).obj ((restrictionAlong α).obj G) where
  val :=
    { app := fun U ↦
        ModuleCat.homMk
          (AddCommGrpCat.ofHom
            { toFun := fun t ↦
                (((extendRestrictAdj α).unit.app ((restrictionAlong α).obj G)).val.app U).hom t
              map_zero' := sorry
              map_add' := sorry })
          sorry
      naturality := sorry }

/-- Unfolding of `extendRestrictUnit` on sections over `U`. -/
theorem extendRestrictUnit_apply {𝒪 𝒪' : Sheaf J CommRingCat.{u}} (α : 𝒪 ⟶ 𝒪')
    (G : ringedSiteModuleCategory J 𝒪') (U : Cᵒᵖ)
    (t : G.val.obj U) :
    ((extendRestrictUnit α G).val.app U).hom t =
      (((extendRestrictAdj α).unit.app ((restrictionAlong α).obj G)).val.app U).hom t :=
  sorry

/-- The inverse comparison `F ⟶ B ⊗_{P_n} F`, as a simplicial map. -/
def restrictedExtendUnit :
    simplicialConstant F ⟶ (extensionDegreewise φ).obj (restrictedModule φ F) where
  app n :=
    extendRestrictUnit ((augmentation φ).app n) F ≫
      (extendAlong ((augmentation φ).app n)).map (evalAtDegreeFromRestricted φ F n)
  naturality := fun {X Y} f => sorry

/-- Sectionwise identity from the degree-`n` evaluation of `cotangentModule` to
`Ω_{P_n/A} ⊗_{P_n} F`. -/
def evalAtDegree_cotangentModule (n : SimplexCategoryᵒᵖ) :
    evalAtDegree (cotangentModule φ F) n ⟶ (degreeSequence φ F n).X₁ where
  val :=
    { app := fun U ↦ ModuleCat.homMk (addCommId ((degreeSequence φ F n).X₁) U) sorry
      naturality := sorry }

/-- `evalAtDegree_cotangentModule` is the identity on underlying sections. -/
theorem evalAtDegree_cotangentModule_apply (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ)
    (t : (evalAtDegree (cotangentModule φ F) n).val.obj U) :
    ((evalAtDegree_cotangentModule φ F n).val.app U).hom t = t :=
  sorry

/-- Degreewise associativity
`B ⊗_{P_n} (Ω_{P_n/A} ⊗_{P_n} F) ⟶ (Ω_{P_n/A} ⊗_{P_n} B) ⊗_B F`. -/
def cotangentExtendDegree (n : SimplexCategoryᵒᵖ) :
    ((extensionDegreewise φ).obj (cotangentModule φ F)).obj n ⟶
      (simplicialCotangent φ F).obj n :=
  (extendAlong ((augmentation φ).app n)).map (evalAtDegree_cotangentModule φ F n) ≫
    ((extendRestrictAdj ((augmentation φ).app n)).homEquiv
        (degreeSequence φ F n).X₁
        (moduleTensor ((simplicialModule A (Under.mk φ)).obj n) F)).symm
      (moduleTensorMap
          ((extendRestrictAdj ((augmentation φ).app n)).unit.app
            (relativeDifferentials (standardTerm A (Under.mk φ) n).hom))
          (𝟙 (restrictedDegree φ F n)) ≫
        Restriction.tensorComparison ((augmentation φ).app n)
          ((simplicialModule A (Under.mk φ)).obj n) F)

/-- Unfolding of `cotangentExtendDegree` as extension of the cotangent evaluation followed by
the adjunction of the restriction tensor comparison. -/
theorem cotangentExtendDegree_eq (n : SimplexCategoryᵒᵖ) :
    cotangentExtendDegree φ F n =
      (extendAlong ((augmentation φ).app n)).map (evalAtDegree_cotangentModule φ F n) ≫
        ((extendRestrictAdj ((augmentation φ).app n)).homEquiv
            (degreeSequence φ F n).X₁
            (moduleTensor ((simplicialModule A (Under.mk φ)).obj n) F)).symm
          (moduleTensorMap
              ((extendRestrictAdj ((augmentation φ).app n)).unit.app
                (relativeDifferentials (standardTerm A (Under.mk φ) n).hom))
              (𝟙 (restrictedDegree φ F n)) ≫
            Restriction.tensorComparison ((augmentation φ).app n)
              ((simplicialModule A (Under.mk φ)).obj n) F) :=
  sorry

/-- Degreewise comparison `extend(Ω_{P_n/A} ⊗ F) ⟶ (extend Ω_{P_n/A}) ⊗ F`. -/
def cotangentExtend :
    (extensionDegreewise φ).obj (cotangentModule φ F) ⟶ simplicialCotangent φ F where
  app n := cotangentExtendDegree φ F n
  naturality := fun {X Y} f => sorry

/-- Degreewise associativity `B ⊗_{P_n} (Ω ⊗ F) ≅ (Ω ⊗ B) ⊗ F` is invertible. -/
instance cotangentExtend_isIso : IsIso (cotangentExtend φ F) :=
  sorry

/-- Sectionwise identity from `Ω_{P_n/A} ⊗_{P_n} F` to the degree-`n` evaluation of
`cotangentModule`. -/
def evalAtDegreeFrom_cotangentModule (n : SimplexCategoryᵒᵖ) :
    (degreeSequence φ F n).X₁ ⟶ evalAtDegree (cotangentModule φ F) n where
  val :=
    { app := fun U ↦ ModuleCat.homMk (addCommId ((degreeSequence φ F n).X₁) U) sorry
      naturality := sorry }

/-- The identity-site coefficient morphism of a same-site map of commutative ring sheaves. -/
def sameSiteCommStructureMap {𝒪 𝒪' : Sheaf J CommRingCat.{u}} (α : 𝒪 ⟶ 𝒪') :
    𝒪 ⟶ ((𝟭 C).sheafPushforwardContinuous CommRingCat.{u} J J).obj 𝒪' :=
  α ≫ (Functor.sheafPushforwardContinuousId CommRingCat.{u} J).inv.app 𝒪'

/-- Unfolding of `sameSiteCommStructureMap`. -/
theorem sameSiteCommStructureMap_eq {𝒪 𝒪' : Sheaf J CommRingCat.{u}} (α : 𝒪 ⟶ 𝒪') :
    sameSiteCommStructureMap α =
      α ≫ (Functor.sheafPushforwardContinuousId CommRingCat.{u} J).inv.app 𝒪' :=
  sorry

/-- Inverse tensor comparison of same-site extension of scalars:
`(extend M) ⊗ (extend N) ⟶ extend (M ⊗ N)`. -/
def extendTensorInv {𝒪 𝒪' : Sheaf J CommRingCat.{u}} (α : 𝒪 ⟶ 𝒪')
    (M N : ringedSiteModuleCategory J 𝒪) :
    moduleTensor ((extendAlong α).obj M) ((extendAlong α).obj N) ⟶
      (extendAlong α).obj (moduleTensor M N) :=
  moduleTensorMap ((pullbackExtendIso α).inv.app M) ((pullbackExtendIso α).inv.app N) ≫
    (SheafOfModules.Pullback.tensorIso (𝟭 C) (sameSiteCommStructureMap α) M N).inv ≫
    (pullbackExtendIso α).hom.app (moduleTensor M N)

/-- Unfolding of `extendTensorInv` through the representably flat pullback tensor isomorphism. -/
theorem extendTensorInv_eq {𝒪 𝒪' : Sheaf J CommRingCat.{u}} (α : 𝒪 ⟶ 𝒪')
    (M N : ringedSiteModuleCategory J 𝒪) :
    extendTensorInv α M N =
      moduleTensorMap ((pullbackExtendIso α).inv.app M)
          ((pullbackExtendIso α).inv.app N) ≫
        (SheafOfModules.Pullback.tensorIso (𝟭 C) (sameSiteCommStructureMap α) M N).inv ≫
        (pullbackExtendIso α).hom.app (moduleTensor M N) :=
  sorry

/-- Reverse degreewise associativity
`(Ω_{P_n/A} ⊗_{P_n} B) ⊗_B F ⟶ B ⊗_{P_n} (Ω_{P_n/A} ⊗_{P_n} F)`. -/
def cotangentExtendInvDegree (n : SimplexCategoryᵒᵖ) :
    (simplicialCotangent φ F).obj n ⟶
      ((extensionDegreewise φ).obj (cotangentModule φ F)).obj n :=
  moduleTensorMap (𝟙 ((simplicialModule A (Under.mk φ)).obj n))
      (extendRestrictUnit ((augmentation φ).app n) F) ≫
    extendTensorInv ((augmentation φ).app n)
      (relativeDifferentials (standardTerm A (Under.mk φ) n).hom)
      (restrictedDegree φ F n) ≫
    (extendAlong ((augmentation φ).app n)).map (evalAtDegreeFrom_cotangentModule φ F n)

/-- Reverse comparison of `cotangentExtend`. -/
def cotangentExtendInv :
    simplicialCotangent φ F ⟶ (extensionDegreewise φ).obj (cotangentModule φ F) where
  app n := cotangentExtendInvDegree φ F n
  naturality := fun {X Y} f => sorry

/-- The Moore complex of the constant simplicial module `F`. -/
def constantComplex : CochainComplex (ringedSiteModuleCategory J B) ℤ :=
  (mooreExtend (B := B)).obj (simplicialConstant F)

/-- The cohomological degree `-n` term of `constantComplex` is `F`. -/
def constantComplex_X (n : ℕ) :
    (constantComplex F).X (-n) ≅ F :=
  extendXIso
    ((alternatingFaceMapComplex (ringedSiteModuleCategory J B)).obj (simplicialConstant F))
    ComplexShape.embeddingDownNat (rfl : ComplexShape.embeddingDownNat.f n = -n)

/-- The degree-zero component of `constantToSingle` is the identification with `F`. -/
def constantComplex_X₀ : (constantComplex F).X 0 ≅ F :=
  constantComplex_X F 0

/-- Differentials into degree `0` of `constantComplex` vanish after the identification with
`F`. -/
theorem constantToSingle_comp (i : ℤ) (hi : (ComplexShape.up ℤ).Rel i 0) :
    (constantComplex F).d i 0 ≫ (constantComplex_X₀ F).hom = 0 :=
  sorry

/-- The quasi-isomorphism from the evaluation complex of `underline{F}` to the degree-zero
single of `F`. -/
def constantToSingle :
    constantComplex F ⟶
      (HomologicalComplex.single (ringedSiteModuleCategory J B) (ComplexShape.up ℤ) 0).obj F :=
  HomologicalComplex.mkHomToSingle (constantComplex_X₀ F).hom (constantToSingle_comp F)

/-- Differentials out of degree `0` of `constantComplex` vanish before the identification with
`F`. -/
theorem singleToConstant_comp (k : ℤ) (hk : (ComplexShape.up ℤ).Rel 0 k) :
    (constantComplex_X₀ F).inv ≫ (constantComplex F).d 0 k = 0 :=
  sorry

/-- The reverse comparison from the degree-zero single of `F` to the Moore complex of
`underline{F}`. -/
def singleToConstant :
    (HomologicalComplex.single (ringedSiteModuleCategory J B) (ComplexShape.up ℤ) 0).obj F ⟶
      constantComplex F :=
  HomologicalComplex.mkHomFromSingle (constantComplex_X₀ F).inv (singleToConstant_comp F)

/-- Lemma 92.4.4: the evaluation complex of `underline{F}` is identified with the degree-zero
single complex of `F`. -/
def constantIsoSingle :
    DerivedCategory.Q.obj (constantComplex F) ≅
      (DerivedCategory.singleFunctor (ringedSiteModuleCategory J B) 0).obj F where
  hom := DerivedCategory.Q.map (constantToSingle F)
  inv := DerivedCategory.Q.map (singleToConstant F)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- `L(φ)` as a cochain complex of `B`-module sheaves. -/
def cotangentCochain :
    CochainComplex (ringedSiteModuleCategory J B) ℤ :=
  (L(φ) : CochainComplex (ringedSiteModuleCategory J B) ℤ)

/-- Unfolding of `cotangentCochain` as a type ascription of `L(φ)`. -/
theorem cotangentCochain_eq :
    cotangentCochain φ = (L(φ) : CochainComplex (ringedSiteModuleCategory J B) ℤ) :=
  sorry

/-- The displayed first vertex `L(φ) ⊗^L F` in `D(B)`. -/
def tensorModule :
    RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J B) :=
  DerivedCategory.DerivedTensor.Bifunctor.obj
    (DerivedCategory.Q.obj (cotangentCochain φ))
    ((DerivedCategory.singleFunctor (ringedSiteModuleCategory J B) 0).obj F)

/-- Unfolding of `tensorModule` as the two-variable derived tensor of `L(φ)` against `F`. -/
theorem tensorModule_eq :
    tensorModule φ F =
      DerivedCategory.DerivedTensor.Bifunctor.obj
        (DerivedCategory.Q.obj (cotangentCochain φ))
        ((DerivedCategory.singleFunctor (ringedSiteModuleCategory J B) 0).obj F) :=
  sorry

/-- The displayed middle vertex `Lπ_!(P¹_{P_•/A}(F))` in `D(B)`. -/
def derivedPrincipalParts :
    RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J B) :=
  (atiyahLowerShriek φ).obj
    ((DerivedCategory.singleFunctor
        (SimplicialSite.ModuleCat (standardSimplicial φ)) 0).obj
      (principalPartsModule φ F))

/-- Unfolding of `derivedPrincipalParts` as `Lπ_!` of the assembled first principal-parts
module. -/
theorem derivedPrincipalParts_eq :
    derivedPrincipalParts φ F =
      (atiyahLowerShriek φ).obj
        ((DerivedCategory.singleFunctor
            (SimplicialSite.ModuleCat (standardSimplicial φ)) 0).obj
          (principalPartsModule φ F)) :=
  sorry

/-- The cohomological degree `-n` term of `tensorCochain` is the `n`-th simplicial cotangent
term. -/
def tensorCochain_X (n : ℕ) :
    (tensorCochain φ F).X (-n) ≅ (simplicialCotangent φ F).obj (op (SimplexCategory.mk n)) :=
  extendXIso
    ((alternatingFaceMapComplex (ringedSiteModuleCategory J B)).obj
      (simplicialCotangent φ F))
    ComplexShape.embeddingDownNat (rfl : ComplexShape.embeddingDownNat.f n = -n)

/-- `tensorCochain` vanishes in strictly positive cohomological degrees. -/
theorem isZero_tensorCochain_X_of_pos {n : ℤ} (hn : 0 < n) :
    IsZero ((tensorCochain φ F).X n) :=
  sorry

/-- The ordinary tensor of `L(φ)` with the degree-zero single of `F` vanishes in strictly
positive cohomological degrees. -/
theorem isZero_cotangentTensorSingle_X_of_pos {n : ℤ} (hn : 0 < n) :
    IsZero
      ((HomologicalComplex.tensorObj (cotangentCochain φ)
        ((HomologicalComplex.single (ringedSiteModuleCategory J B)
          (ComplexShape.up ℤ) 0).obj F)).X n) :=
  sorry

/-- The total-complex shape sends `(-n.natAbs, 0)` to `n` when `n = -n.natAbs`. -/
theorem π_up_neg_natAbs (n : ℤ) (hn : n = -n.natAbs) :
    ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (-(n.natAbs : ℤ), 0) = n :=
  sorry

/-- The summand inclusion of `L(φ).X (-n.natAbs) ⊗ F` into the tensor with the degree-zero
single of `F`. -/
def ιTensorCotangentSingle (n : ℤ) (hn : n = -n.natAbs) :
    (moduleTensor ((cotangentCochain φ).X (-(n.natAbs : ℤ)))
      (((HomologicalComplex.single (ringedSiteModuleCategory J B)
          (ComplexShape.up ℤ) 0).obj F).X 0)) ⟶
      (HomologicalComplex.tensorObj (cotangentCochain φ)
        ((HomologicalComplex.single (ringedSiteModuleCategory J B)
          (ComplexShape.up ℤ) 0).obj F)).X n :=
  HomologicalComplex.ιTensorObj (cotangentCochain φ)
    ((HomologicalComplex.single (ringedSiteModuleCategory J B) (ComplexShape.up ℤ) 0).obj F)
    (-(n.natAbs : ℤ)) 0 n (π_up_neg_natAbs n hn)

/-- The summand inclusion `ιTensorCotangentSingle` is invertible. -/
instance ιTensorCotangentSingle_isIso (n : ℤ) (hn : n = -n.natAbs) :
    IsIso (ιTensorCotangentSingle φ F n hn) :=
  sorry

/-- Unfolding of `ιTensorCotangentSingle` as a total-complex summand inclusion. -/
theorem ιTensorCotangentSingle_eq (n : ℤ) (hn : n = -n.natAbs) :
    ιTensorCotangentSingle φ F n hn =
      HomologicalComplex.ιTensorObj (cotangentCochain φ)
        ((HomologicalComplex.single (ringedSiteModuleCategory J B)
            (ComplexShape.up ℤ) 0).obj F)
        (-(n.natAbs : ℤ)) 0 n (π_up_neg_natAbs n hn) :=
  sorry

/-- A non-positive integer equals the negation of its `natAbs`. -/
theorem eq_neg_natAbs_of_not_pos {n : ℤ} (hn : ¬ 0 < n) : n = -n.natAbs :=
  sorry

/-- The `(i₁, i₂)`-summand of `L(φ) ⊗ single F` in degree `n` identifies with the
`( -n.natAbs, 0 )` summand when those indices match. -/
theorem tensorCotangentSingle_component_eq (n : ℤ) (hn : n = -n.natAbs)
    (i₁ i₂ : ℤ) (h : i₁ = -(n.natAbs : ℤ) ∧ i₂ = 0)
    (hi : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (i₁, i₂) = n) :
    moduleTensor ((cotangentCochain φ).X i₁)
        (((HomologicalComplex.single (ringedSiteModuleCategory J B)
          (ComplexShape.up ℤ) 0).obj F).X i₂) =
      moduleTensor ((cotangentCochain φ).X (-(n.natAbs : ℤ)))
        (((HomologicalComplex.single (ringedSiteModuleCategory J B)
          (ComplexShape.up ℤ) 0).obj F).X 0) :=
  sorry

/-- The inverse of the summand inclusion `ιTensorCotangentSingle`, as the matching
total-complex projection. -/
def πTensorCotangentSingle (n : ℤ) (hn : n = -n.natAbs) :
    (HomologicalComplex.tensorObj (cotangentCochain φ)
      ((HomologicalComplex.single (ringedSiteModuleCategory J B)
        (ComplexShape.up ℤ) 0).obj F)).X n ⟶
      moduleTensor ((cotangentCochain φ).X (-(n.natAbs : ℤ)))
        (((HomologicalComplex.single (ringedSiteModuleCategory J B)
          (ComplexShape.up ℤ) 0).obj F).X 0) :=
  HomologicalComplex.mapBifunctorDesc
    (fun i₁ i₂ hi =>
      dite (i₁ = -(n.natAbs : ℤ) ∧ i₂ = 0)
        (fun h =>
          eqToHom (tensorCotangentSingle_component_eq φ F n hn i₁ i₂ h hi))
        (fun _ => 0))

/-- Degreewise identification of `tensorCochain` with `L(φ) ⊗ single F`. -/
def tensorCochainXIsoTensorSingle (n : ℤ) :
    (tensorCochain φ F).X n ≅
      (HomologicalComplex.tensorObj (cotangentCochain φ)
        ((HomologicalComplex.single (ringedSiteModuleCategory J B)
          (ComplexShape.up ℤ) 0).obj F)).X n :=
  dite (0 < n)
    (fun hn =>
      IsZero.iso (isZero_tensorCochain_X_of_pos φ F hn)
        (isZero_cotangentTensorSingle_X_of_pos φ F hn))
    (fun hn =>
      let hn' := eq_neg_natAbs_of_not_pos hn
      HomologicalComplex.XIsoOfEq (tensorCochain φ F) hn' ≪≫
        tensorCochain_X φ F n.natAbs ≪≫
        (tensorRight F).mapIso
          (objXIso A (Under.mk φ) n.natAbs).symm ≪≫
        (whiskerLeftIso ((cotangentCochain φ).X (-(n.natAbs : ℤ)))
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).symm) ≪≫
        { hom := ιTensorCotangentSingle φ F n hn'
          inv := πTensorCotangentSingle φ F n hn'
          hom_inv_id := sorry
          inv_hom_id := sorry })

/-- In positive degrees, `tensorCochainXIsoTensorSingle` is the unique map of zero objects. -/
theorem tensorCochainXIsoTensorSingle_of_pos {n : ℤ} (hn : 0 < n) :
    tensorCochainXIsoTensorSingle φ F n =
      IsZero.iso (isZero_tensorCochain_X_of_pos φ F hn)
        (isZero_cotangentTensorSingle_X_of_pos φ F hn) :=
  sorry

/-- Cochain-level identification `Moore((Ω_{P_•/A} ⊗ B) ⊗ F) ≅ L(φ) ⊗ single F`. -/
def tensorCochainIsoTensorSingle :
    tensorCochain φ F ≅
      HomologicalComplex.tensorObj (cotangentCochain φ)
        ((HomologicalComplex.single (ringedSiteModuleCategory J B)
          (ComplexShape.up ℤ) 0).obj F) :=
  HomologicalComplex.Hom.isoOfComponents (tensorCochainXIsoTensorSingle φ F)
    (fun _ _ _ => sorry)

/-- The degree-`n` component of `tensorCochainIsoTensorSingle` is
`tensorCochainXIsoTensorSingle`. -/
theorem tensorCochainIsoTensorSingle_hom_f (n : ℤ) :
    (tensorCochainIsoTensorSingle φ F).hom.f n =
      (tensorCochainXIsoTensorSingle φ F n).hom :=
  sorry

/-- The two-variable derived-tensor counit at the cochain models of `L(φ)` and `F`. -/
def tensorCounitApp :
    DerivedCategory.DerivedTensor.Bifunctor.obj
        (DerivedCategory.Q.obj (cotangentCochain φ))
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (ringedSiteModuleCategory J B)
            (ComplexShape.up ℤ) 0).obj F)) ⟶
      DerivedCategory.Q.obj
        (HomologicalComplex.tensorObj (cotangentCochain φ)
          ((HomologicalComplex.single (ringedSiteModuleCategory J B)
            (ComplexShape.up ℤ) 0).obj F)) :=
  DerivedCategory.DerivedTensor.Bifunctor.counitAppOfQ
    (cotangentCochain φ)
    ((HomologicalComplex.single (ringedSiteModuleCategory J B)
      (ComplexShape.up ℤ) 0).obj F)

/-- The two-variable derived-tensor counit at the cochain models of `L(φ)` and `F` is a
quasi-isomorphism on its actual homotopy representative. -/
theorem tensorCounitApp_quasiIso :
    HomotopyCategory.quasiIso (ringedSiteModuleCategory J B) (ComplexShape.up ℤ)
      (comparisonArrow (tensorCounitApp φ F)).hom :=
  sorry

/-- Identification of the two-variable derived tensor of the cochain models with ordinary
tensor, by inverting the counit through the localization formal inverse. -/
def tensorCounitAppIso :
    DerivedCategory.DerivedTensor.Bifunctor.obj
        (DerivedCategory.Q.obj (cotangentCochain φ))
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (ringedSiteModuleCategory J B)
            (ComplexShape.up ℤ) 0).obj F)) ≅
      DerivedCategory.Q.obj
        (HomologicalComplex.tensorObj (cotangentCochain φ)
          ((HomologicalComplex.single (ringedSiteModuleCategory J B)
            (ComplexShape.up ℤ) 0).obj F)) :=
  comparisonFormalIso (tensorCounitApp φ F) (tensorCounitApp_quasiIso φ F)

/-- Transport of the second derived-tensor factor from `Q (single F)` to `single F`. -/
def tensorModuleIsoBifunctorQ :
    DerivedCategory.DerivedTensor.Bifunctor.obj
        (DerivedCategory.Q.obj (cotangentCochain φ))
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (ringedSiteModuleCategory J B)
            (ComplexShape.up ℤ) 0).obj F)) ≅
      tensorModule φ F :=
  (DerivedCategory.DerivedTensor.Bifunctor.leftFunctor
      (DerivedCategory.Q.obj (cotangentCochain φ))).mapIso
    ((DerivedCategory.singleFunctorIsoCompQ (ringedSiteModuleCategory J B) 0).app F)

/-- Comparison `Lπ_!(single X) ⟶ evaluation (single (extend X))` from the homotopy-to-derived
counit after Moore evaluation. -/
def atiyahLowerShriekToMoore
    (X : SimplicialSite.ModuleCat (J := J) (standardSimplicial φ)) :
    (atiyahLowerShriek φ).obj
        ((DerivedCategory.singleFunctor
            (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ)) 0).obj X) ⟶
      (evaluation (B := B)).obj
        ((DerivedCategory.singleFunctor
            (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B) 0).obj
          ((extensionDegreewise φ).obj X)) :=
  (evaluation (B := B)).map (derivedExtensionSingle φ X)

/-- Unfolding of `atiyahLowerShriekToMoore` as Moore evaluation of `derivedExtensionSingle`. -/
theorem atiyahLowerShriekToMoore_eq
    (X : SimplicialSite.ModuleCat (J := J) (standardSimplicial φ)) :
    atiyahLowerShriekToMoore φ X =
      (evaluation (B := B)).map (derivedExtensionSingle φ X) :=
  sorry

/-- The comparison isomorphism `Lπ_!(Ω_{P_•/A} ⊗ F) ≅ L(φ) ⊗^L F`. -/
def tensorIso :
    (atiyahTriangle_ofSES φ F).obj₁ ≅ tensorModule φ F where
  hom :=
    atiyahLowerShriekToMoore φ (cotangentModule φ F) ≫
        (evaluation (B := B)).map
          ((DerivedCategory.singleFunctor
              (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B) 0).map
            (cotangentExtend φ F)) ≫
          (evaluationSingleIso (B := B) (simplicialCotangent φ F)).hom ≫
            DerivedCategory.Q.map (tensorCochainIsoTensorSingle φ F).hom ≫
              (tensorCounitAppIso φ F).inv ≫
                (tensorModuleIsoBifunctorQ φ F).hom
  inv :=
    (tensorModuleIsoBifunctorQ φ F).inv ≫
      (tensorCounitAppIso φ F).hom ≫
        DerivedCategory.Q.map (tensorCochainIsoTensorSingle φ F).inv ≫
          (evaluationSingleIso (B := B) (simplicialCotangent φ F)).inv ≫
            (evaluation (B := B)).map
              ((DerivedCategory.singleFunctor
                  (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B) 0).map
                (cotangentExtendInv φ F)) ≫
              cotangentComparisonInv φ F
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward comparison morphism `Lπ_!(Ω_{P_•/A} ⊗ F) ⟶ L(φ) ⊗^L F`. -/
def tensorIso_hom :
    (atiyahTriangle_ofSES φ F).obj₁ ⟶ tensorModule φ F :=
  (tensorIso φ F).hom

/-- The inverse comparison morphism `L(φ) ⊗^L F ⟶ Lπ_!(Ω_{P_•/A} ⊗ F)`. -/
def tensorIso_inv :
    tensorModule φ F ⟶ (atiyahTriangle_ofSES φ F).obj₁ :=
  (tensorIso φ F).inv

/-- The comparison isomorphism `Lπ_!(restricted F) ≅ F`. -/
def moduleIso :
    (atiyahTriangle_ofSES φ F).obj₃ ≅
      (DerivedCategory.singleFunctor (ringedSiteModuleCategory J B) 0).obj F where
  hom :=
    atiyahLowerShriekToMoore φ (restrictedModule φ F) ≫
        (evaluation (B := B)).map
          ((DerivedCategory.singleFunctor
              (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B) 0).map
            (restrictedExtendCounit φ F)) ≫
          (evaluationSingleIso (B := B) (simplicialConstant F)).hom ≫
            (constantIsoSingle F).hom
  inv :=
    (constantIsoSingle F).inv ≫
      (evaluationSingleIso (B := B) (simplicialConstant F)).inv ≫
        (evaluation (B := B)).map
          ((DerivedCategory.singleFunctor
              (SimplexCategoryᵒᵖ ⥤ ringedSiteModuleCategory J B) 0).map
            (restrictedExtendUnit φ F)) ≫
          restrictedComparisonInv φ F
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward comparison morphism `Lπ_!(restricted F) ⟶ single F`. -/
def moduleIso_hom :
    (atiyahTriangle_ofSES φ F).obj₃ ⟶
      (DerivedCategory.singleFunctor (ringedSiteModuleCategory J B) 0).obj F :=
  (moduleIso φ F).hom

/-- The inverse comparison morphism `single F ⟶ Lπ_!(restricted F)`. -/
def moduleIso_inv :
    (DerivedCategory.singleFunctor (ringedSiteModuleCategory J B) 0).obj F ⟶
      (atiyahTriangle_ofSES φ F).obj₃ :=
  (moduleIso φ F).inv

/-- The first map `L(φ) ⊗^L F ⟶ Lπ_!(P¹_{P_•/A}(F))` of the displayed triangle. -/
def tensorToPrincipalParts :
    tensorModule φ F ⟶ derivedPrincipalParts φ F :=
  (tensorIso φ F).inv ≫ (atiyahTriangle_ofSES φ F).mor₁

/-- Unfolding of `tensorToPrincipalParts` by conjugating the SES-triangle first map. -/
theorem tensorToPrincipalParts_eq :
    tensorToPrincipalParts φ F =
      (tensorIso φ F).inv ≫ (atiyahTriangle_ofSES φ F).mor₁ :=
  sorry

/-- The second map `Lπ_!(P¹_{P_•/A}(F)) ⟶ F` of the displayed triangle. -/
def principalPartsToModule :
    derivedPrincipalParts φ F ⟶
      (DerivedCategory.singleFunctor (ringedSiteModuleCategory J B) 0).obj F :=
  (atiyahTriangle_ofSES φ F).mor₂ ≫ (moduleIso φ F).hom

/-- Unfolding of `principalPartsToModule` by conjugating the SES-triangle second map. -/
theorem principalPartsToModule_eq :
    principalPartsToModule φ F =
      (atiyahTriangle_ofSES φ F).mor₂ ≫ (moduleIso φ F).hom :=
  sorry

/-- The degree-zero single of the assembled simplicial principal-parts sequence. -/
def atiyahSequence_singleComplex :
    ShortComplex
      (CochainComplex (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ)) ℤ) :=
  (HomologicalComplex.single
      (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ))
      (ComplexShape.up ℤ) 0).mapShortComplex.obj (atiyahSequence φ F)

/-- Unfolding of `atiyahSequence_singleComplex` as the degree-zero single of `atiyahSequence`. -/
theorem atiyahSequence_singleComplex_eq :
    atiyahSequence_singleComplex φ F =
      (HomologicalComplex.single
          (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ))
          (ComplexShape.up ℤ) 0).mapShortComplex.obj (atiyahSequence φ F) :=
  sorry

/-- The mapping-cone description of the third vertex of the degree-zero single sequence. -/
def atiyahSequence_desc :
    CochainComplex.mappingCone (atiyahSequence_singleComplex φ F).f ⟶
      (atiyahSequence_singleComplex φ F).X₃ :=
  CochainComplex.mappingCone.descShortComplex (atiyahSequence_singleComplex φ F)

/-- Unfolding of `atiyahSequence_desc` as the mapping-cone description of the single sequence. -/
theorem atiyahSequence_desc_eq :
    atiyahSequence_desc φ F =
      CochainComplex.mappingCone.descShortComplex (atiyahSequence_singleComplex φ F) :=
  sorry

/-- `atiyahSequence_desc` is a quasi-isomorphism. -/
theorem atiyahSequence_desc_quasiIso :
    HomologicalComplex.quasiIso
      (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ))
      (ComplexShape.up ℤ) (atiyahSequence_desc φ F) :=
  sorry

/-- Localization inverse of the concrete mapping-cone description. -/
def atiyahSequence_descIso :=
  CategoryTheory.Localization.isoOfHom
    (DerivedCategory.Q :
      CochainComplex (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ)) ℤ ⥤
        DerivedCategory (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ)))
    (HomologicalComplex.quasiIso
      (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ))
      (ComplexShape.up ℤ))
    (atiyahSequence_desc φ F) (atiyahSequence_desc_quasiIso φ F)

/-- Unfolding of `atiyahSequence_descIso` as `Localization.isoOfHom` of `atiyahSequence_desc`. -/
theorem atiyahSequence_descIso_eq :
    atiyahSequence_descIso φ F =
      CategoryTheory.Localization.isoOfHom
        (DerivedCategory.Q :
          CochainComplex (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ)) ℤ ⥤
            DerivedCategory (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ)))
        (HomologicalComplex.quasiIso
          (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ))
          (ComplexShape.up ℤ))
        (atiyahSequence_desc φ F) (atiyahSequence_desc_quasiIso φ F) :=
  sorry

/-- The SES connecting map in `D(P_•)`, obtained from the mapping cone of `atiyahSequence_f`
by inverting the concrete quasi-isomorphism `atiyahSequence_desc`. -/
def atiyahSequence_connecting :
    (DerivedCategory.singleFunctor
        (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ)) 0).obj
      (restrictedModule φ F) ⟶
      ((DerivedCategory.singleFunctor
          (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ)) 0).obj
        (cotangentModule φ F))⟦(1 : ℤ)⟧ :=
  (DerivedCategory.singleFunctorIsoCompQ
      (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ)) 0).hom.app
    (restrictedModule φ F) ≫
  (atiyahSequence_descIso φ F).inv ≫
  DerivedCategory.Q.map
    (CochainComplex.mappingCone.triangle
      ((HomologicalComplex.single
          (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ))
          (ComplexShape.up ℤ) 0).map (atiyahSequence_f φ F))).mor₃ ≫
  (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
    ((HomologicalComplex.single
        (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ))
        (ComplexShape.up ℤ) 0).obj (cotangentModule φ F)) ≫
  ((DerivedCategory.singleFunctorIsoCompQ
      (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ)) 0).inv.app
    (cotangentModule φ F))⟦(1 : ℤ)⟧'

/-- Unfolding of `atiyahSequence_connecting` from the mapping-cone boundary. -/
theorem atiyahSequence_connecting_eq :
    atiyahSequence_connecting φ F =
      (DerivedCategory.singleFunctorIsoCompQ
          (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ)) 0).hom.app
        (restrictedModule φ F) ≫
      (atiyahSequence_descIso φ F).inv ≫
      DerivedCategory.Q.map
        (CochainComplex.mappingCone.triangle
          ((HomologicalComplex.single
              (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ))
              (ComplexShape.up ℤ) 0).map (atiyahSequence_f φ F))).mor₃ ≫
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
        ((HomologicalComplex.single
            (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ))
            (ComplexShape.up ℤ) 0).obj (cotangentModule φ F)) ≫
      ((DerivedCategory.singleFunctorIsoCompQ
          (SimplicialSite.ModuleCat (J := J) (standardSimplicial φ)) 0).inv.app
        (cotangentModule φ F))⟦(1 : ℤ)⟧' :=
  sorry

/-- The connecting map `F ⟶ (L(φ) ⊗^L F)⟦1⟧` of the displayed triangle. -/
def connectingMap :
    (DerivedCategory.singleFunctor (ringedSiteModuleCategory J B) 0).obj F ⟶
      (tensorModule φ F)⟦(1 : ℤ)⟧ :=
  (moduleIso φ F).inv ≫
    (atiyahTriangle_ofSES φ F).mor₃ ≫
      (shiftFunctor (RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J B))
          (1 : ℤ)).map (tensorIso φ F).hom

/-- Unfolding of `connectingMap` by conjugating the SES-triangle connecting map. -/
theorem connectingMap_eq :
    connectingMap φ F =
      (moduleIso φ F).inv ≫
        (atiyahTriangle_ofSES φ F).mor₃ ≫
          (shiftFunctor (RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J B))
              (1 : ℤ)).map (tensorIso φ F).hom :=
  sorry

/-- The displayed distinguished triangle
`L(φ) ⊗^L F ⟶ Lπ_!(P¹_{P_•/A}(F)) ⟶ F ⟶ (L(φ) ⊗^L F)⟦1⟧` in `D(B)`. -/
def atiyahTriangle :
    Triangle (RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J B)) :=
  Triangle.mk (tensorToPrincipalParts φ F) (principalPartsToModule φ F)
    (connectingMap φ F)

/-- The first vertex of `atiyahTriangle` is `tensorModule`. -/
theorem atiyahTriangle_obj₁ :
    (atiyahTriangle φ F).obj₁ = tensorModule φ F :=
  sorry

/-- The second vertex of `atiyahTriangle` is `derivedPrincipalParts`. -/
theorem atiyahTriangle_obj₂ :
    (atiyahTriangle φ F).obj₂ = derivedPrincipalParts φ F :=
  sorry

/-- The third vertex of `atiyahTriangle` is the image of `F` under the degree-zero single
functor. -/
theorem atiyahTriangle_obj₃ :
    (atiyahTriangle φ F).obj₃ =
      (DerivedCategory.singleFunctor (ringedSiteModuleCategory J B) 0).obj F :=
  sorry

/-- The first morphism of `atiyahTriangle` is `tensorToPrincipalParts`. -/
theorem atiyahTriangle_mor₁ :
    (atiyahTriangle φ F).mor₁ = tensorToPrincipalParts φ F :=
  sorry

/-- The second morphism of `atiyahTriangle` is `principalPartsToModule`. -/
theorem atiyahTriangle_mor₂ :
    (atiyahTriangle φ F).mor₂ = principalPartsToModule φ F :=
  sorry

/-- The third morphism of `atiyahTriangle` is `connectingMap`. -/
theorem atiyahTriangle_mor₃ :
    (atiyahTriangle φ F).mor₃ = connectingMap φ F :=
  sorry

/-- The Atiyah triangle of `F` along `φ` is distinguished in `D(B)`. -/
theorem atiyahTriangle_distinguished :
    atiyahTriangle φ F ∈
      distTriang (RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J B)) :=
  sorry

end SheafOfModules.RingedSite.CotangentComplex
