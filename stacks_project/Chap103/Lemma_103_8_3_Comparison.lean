/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import stacks_project.Chap103.Lemma_103_8_3_LiftedRestriction
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.ExactSquare
public import ReasLib.CategoryTheory.Fibered.Groupoids.UnderlyingFunctorIso
public import stacks_project.Chap96.«96_10_3_1_Comparison»
public import stacks_project.Chap103.Definition_103_7_1_FlatBaseChange
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap101.Definition_101_4_1_Separation

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.GroupoidsOver FiberedCategoryOver.Groupoids
open scoped Bicategory
noncomputable section
universe u
namespace AlgebraicGeometry.GroupoidsOver.HigherDirectImageComparison
variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) (y : Y.total)
variable (U : AlgebraicSpace S) (fU : U ⟶ AlgebraicSpace.ofOver (Y.p.obj y))
variable (eU : U.toGroupoids ≌ TwoFibreProduct.apex.{u + 1, u, u + 1, u} (moduleSliceHom y) f)
variable (h_fst : eU.symm.hom ≫ AlgebraicSpace.toGroupoids.map fU ≫
    (AlgebraicSpace.ofOverSliceEquiv (Y.p.obj y)).hom ≅
      TwoFibreProduct.fst.{u + 1, u, u + 1, u} (moduleSliceHom y) f)

/-- First projection of the specified geometric fibre product. -/
abbrev fst := TwoFibreProduct.fst.{u + 1, u, u + 1, u} (moduleSliceHom y) f
/-- Second projection of the specified geometric fibre product. -/
abbrev snd := TwoFibreProduct.snd.{u + 1, u, u + 1, u} (moduleSliceHom y) f
/-- The original target scheme represented as its slice groupoid. -/
abbrev eV := AlgebraicSpace.ofOverSliceEquiv (Y.p.obj y)

/-- The original coefficient restricted along the actual second projection and presentation. -/
def coefficient : EtaleModulesLift X ⥤ AlgebraicSpace.Modules.Lift U :=
  moduleInverseImageLift (snd f y) ⋙ moduleRepresentingRestrictionLift eU

/-- The given representing triangle, cancelled using its actual unit. -/
def presentationCell : eU.hom ≫ fst f y ≅ AlgebraicSpace.toGroupoids.map fU ≫ (eV y).hom :=
  Bicategory.whiskerLeftIso eU.hom h_fst.symm ≪≫
    (α_ eU.hom eU.inv (AlgebraicSpace.toGroupoids.map fU ≫ (eV y).hom)).symm ≪≫
    Bicategory.whiskerRightIso eU.unit.symm (AlgebraicSpace.toGroupoids.map fU ≫ (eV y).hom) ≪≫
    λ_ (AlgebraicSpace.toGroupoids.map fU ≫ (eV y).hom)

/-- The supplied representing triangle on actual total-category functors. -/
def presentationFunctorIso : toFunctor eU.hom ⋙ toFunctor (fst f y) ≅
    toFunctor (AlgebraicSpace.toGroupoids.map fU) ⋙ toFunctor (eV y).hom :=
  (eqToIso (toFunctor.comp eU.hom (fst f y))).symm ≪≫
    toFunctorIso (presentationCell f y U fU eU h_fst) ≪≫
    eqToIso (toFunctor.comp (AlgebraicSpace.toGroupoids.map fU) (eV y).hom)

/-- The small comma arrow is retained through the first projection. -/
def firstArrow (b : (AlgebraicSpace.ofOver (Y.p.obj y)).smallEtaleSite)
    (q : AlgebraicSpace.compareSmallIndex fU b) :
    (toFunctor (fst f y)).obj ((smallEtaleFunctor U _ eU).obj q.right.unop) ⟶
      (smallEtaleFunctor _ _ (eV y)).obj b :=
  (presentationFunctorIso f y U fU eU h_fst).hom.app (toGroupoidsObj q.right.unop) ≫
    (toFunctor (eV y).hom).map (AlgebraicSpace.compareIndexHom fU q)

/-- The actual fibre-product cell on total-category functors. -/
def squareFunctorIso : toFunctor (snd f y) ⋙ toFunctor f ≅
    toFunctor (fst f y) ⋙ toFunctor (moduleSliceHom y) :=
  (eqToIso (toFunctor.comp (snd f y) f)).symm ≪≫
    (toFunctorIso (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} (moduleSliceHom y) f)).symm ≪≫
    eqToIso (toFunctor.comp (fst f y) (moduleSliceHom y))

/-- The genuine BIG comma arrow supplied by the fibre-product cell and q. -/
def bigArrow (b : (AlgebraicSpace.ofOver (Y.p.obj y)).smallEtaleSite)
    (q : AlgebraicSpace.compareSmallIndex fU b) :
    (toFunctor f).obj ((toFunctor (snd f y)).obj ((smallEtaleFunctor U _ eU).obj q.right.unop)) ⟶
      (toFunctor (moduleSliceHom y)).obj ((smallEtaleFunctor _ _ (eV y)).obj b) :=
  (squareFunctorIso f y).hom.app ((smallEtaleFunctor U _ eU).obj q.right.unop) ≫
    (toFunctor (moduleSliceHom y)).map (firstArrow f y U fU eU h_fst b q)

/-- Evaluate the canonical BIG direct image at a specified geometric comma arrow. -/
def bigEvaluation (M : EtaleModulesLift X) (V : Y.total) (a : X.total)
    (g : (toFunctor f).obj a ⟶ V) :
    ((moduleDirectImageLift f).obj M).val.obj (op V) → M.val.obj (op a) := by
  -- Local instance justification (proof-local temporary data): evaluate the canonical factory using its proved type sheafification.
  letI := SiteUniverse.types X.etaleTopology
  -- Local instance justification (defeq pin): use the actual full comma limits selected in the canonical BIG direct image.
  letI (P : X.totalᵒᵖ ⥤ Type (u + 1)) := SiteUniverse.rightKan (toFunctor f) P
  let Q := (CategoryTheory.Sheaf.InternalModule.ToInternal.underlying
    (commEtaleRingedSiteLift X).structureSheaf).obj M
  let k := ((RingedSite.ToposHom.ModulePushforward.forgetIso (moduleDirectImageToposHomLift f)).hom.app M).hom.app (op V)
  let t := ((toFunctor f).op.ranObjObjIsoLimit Q.obj (op V)).hom ≫
    limit.π (StructuredArrow.proj (op V) (toFunctor f).op ⋙ Q.obj) (StructuredArrow.mk g.op)
  exact fun x => t (k x)

/-- The comma diagram whose limit computes small-site pushforward sections at `b`. -/
abbrev smallPushforwardDiagram (M : EtaleModulesLift X)
    (b : (AlgebraicSpace.ofOver (Y.p.obj y)).smallEtaleSite) :=
  StructuredArrow.proj (op ((AlgebraicSpace.etaleBaseChange fU).obj b))
    (AlgebraicSpace.smallEtaleToSpaces U).op ⋙
    ((CategoryTheory.Sheaf.InternalModule.ToInternal.underlying
      (AlgebraicSpace.commRingedSiteLift U).structureSheaf).obj
      ((coefficient f y U eU).obj M)).obj

/-- The family of BIG evaluations at the comma arrows over `b`. -/
def underivedValueFamily (M : EtaleModulesLift X)
    (b : (AlgebraicSpace.ofOver (Y.p.obj y)).smallEtaleSite)
    (s : ((moduleAtObjectLift y).obj ((moduleDirectImageLift f).obj M)).val.obj (op b))
    (q : StructuredArrow (op ((AlgebraicSpace.etaleBaseChange fU).obj b))
      (AlgebraicSpace.smallEtaleToSpaces U).op) :=
  bigEvaluation f M
    ((toFunctor (moduleSliceHom y)).obj ((smallEtaleFunctor _ _ (eV y)).obj b))
    ((toFunctor (snd f y)).obj ((smallEtaleFunctor U _ eU).obj q.right.unop))
    (bigArrow f y U fU eU h_fst b q) s

/-- The BIG evaluations form a cone on the small-site comma diagram. -/
theorem underivedValue_isSection (M : EtaleModulesLift X)
    (b : (AlgebraicSpace.ofOver (Y.p.obj y)).smallEtaleSite)
    (s : ((moduleAtObjectLift y).obj ((moduleDirectImageLift f).obj M)).val.obj (op b)) :
    ∀ q q' (φ : q ⟶ q'),
      (smallPushforwardDiagram f y U fU eU M b).map φ
        (underivedValueFamily f y U fU eU h_fst M b s q) =
      underivedValueFamily f y U fU eU h_fst M b s q' :=
  sorry

/-- The actual section map lands directly in the CANONICAL small-site pushforward:
its limit element is the family of the displayed BIG evaluations. -/
def underivedValue (M : EtaleModulesLift X)
    (b : (AlgebraicSpace.ofOver (Y.p.obj y)).smallEtaleSite)
    (s : ((moduleAtObjectLift y).obj ((moduleDirectImageLift f).obj M)).val.obj (op b)) :
    ((AlgebraicSpace.Modules.pushforwardLift fU).obj ((coefficient f y U eU).obj M)).val.obj (op b) :=
  let N := (coefficient f y U eU).obj M
  let Q := (CategoryTheory.Sheaf.InternalModule.ToInternal.underlying
    (AlgebraicSpace.commRingedSiteLift U).structureSheaf).obj N
  let v := op ((AlgebraicSpace.etaleBaseChange fU).obj b)
  let i := AlgebraicSpace.smallEtaleToSpaces U
  let z := Types.Limit.mk (smallPushforwardDiagram f y U fU eU M b)
    (underivedValueFamily f y U fU eU h_fst M b s)
    (underivedValue_isSection f y U fU eU h_fst M b s)
  let ranValue := (i.op.ranObjObjIsoLimit Q.obj v).inv z
  ((RingedSite.ToposHom.ModulePushforward.forgetIso
    (AlgebraicSpace.ringedToposHomLift fU)).inv.app N).hom.app (op b) ranValue

/-- Additivity of the underived section comparison at a small-étale object. -/
theorem underivedValue_map_add (M : EtaleModulesLift X)
    (b : (AlgebraicSpace.ofOver (Y.p.obj y)).smallEtaleSite)
    (x x' : ((moduleAtObjectLift y).obj ((moduleDirectImageLift f).obj M)).val.obj (op b)) :
    underivedValue f y U fU eU h_fst M b (x + x') =
      underivedValue f y U fU eU h_fst M b x +
        underivedValue f y U fU eU h_fst M b x' :=
  sorry

/-- Scalar compatibility of the underived section comparison at a small-étale object. -/
theorem underivedValue_map_smul (M : EtaleModulesLift X)
    (b : (AlgebraicSpace.ofOver (Y.p.obj y)).smallEtaleSite)
    (r : ((AlgebraicSpace.ofOver (Y.p.obj y)).commRingedSiteLift.structureSheaf.obj.obj
        (op b)))
    (x : ((moduleAtObjectLift y).obj ((moduleDirectImageLift f).obj M)).val.obj (op b)) :
    underivedValue f y U fU eU h_fst M b (r • x) =
      r • underivedValue f y U fU eU h_fst M b x :=
  sorry

/-- Package a section-wise function as a morphism of lifted modules. -/
def moduleCatHomOfFun {R : Type (u + 1)} [Ring R]
    (src tgt : ModuleCat.{u + 1} R) (toFun : src → tgt)
    (map_add' : ∀ x x', toFun (x + x') = toFun x + toFun x')
    (map_smul' : ∀ (r : R) (x : src), toFun (r • x) = r • toFun x) : src ⟶ tgt :=
  ModuleCat.ofHom
    { toFun := toFun
      map_add' := map_add'
      map_smul' := map_smul' }

/-- `moduleCatHomOfFun` applies as the supplied section function. -/
theorem moduleCatHomOfFun_apply {R : Type (u + 1)} [Ring R]
    (src tgt : ModuleCat.{u + 1} R) (toFun : src → tgt)
    (map_add' : ∀ x x', toFun (x + x') = toFun x + toFun x')
    (map_smul' : ∀ (r : R) (x : src), toFun (r • x) = r • toFun x) (x : src) :
    moduleCatHomOfFun src tgt toFun map_add' map_smul' x = toFun x :=
  sorry

/-- The underived comparison as a module homomorphism on sections over `b`. -/
def underivedAppHom (M : EtaleModulesLift X)
    (b : ((AlgebraicSpace.ofOver (Y.p.obj y)).smallEtaleSite)ᵒᵖ) :
    ((moduleAtObjectLift y).obj ((moduleDirectImageLift f).obj M)).val.obj b ⟶
      ((AlgebraicSpace.Modules.pushforwardLift fU).obj ((coefficient f y U eU).obj M)).val.obj b :=
  moduleCatHomOfFun
    (((moduleAtObjectLift y).obj ((moduleDirectImageLift f).obj M)).val.obj b)
    (((AlgebraicSpace.Modules.pushforwardLift fU).obj ((coefficient f y U eU).obj M)).val.obj b)
    (underivedValue f y U fU eU h_fst M b.unop)
    (underivedValue_map_add f y U fU eU h_fst M b.unop)
    (underivedValue_map_smul f y U fU eU h_fst M b.unop)

/-- Naturality of `underivedAppHom` in the small-étale object. -/
theorem underivedAppHom_naturality (M : EtaleModulesLift X)
    {b b' : ((AlgebraicSpace.ofOver (Y.p.obj y)).smallEtaleSite)ᵒᵖ} (φ : b ⟶ b') :
    ((moduleAtObjectLift y).obj ((moduleDirectImageLift f).obj M)).val.map φ ≫
        (ModuleCat.restrictScalars
          (((AlgebraicSpace.ofOver (Y.p.obj y)).commRingedSiteLift.structureSheaf.obj.map φ).hom)).map
          (underivedAppHom f y U fU eU h_fst M b') =
      underivedAppHom f y U fU eU h_fst M b ≫
        ((AlgebraicSpace.Modules.pushforwardLift fU).obj
          ((coefficient f y U eU).obj M)).val.map φ :=
  sorry

/-- The section functions above are packaged with their fixed linearity and naturality laws. -/
def underivedApp (M : EtaleModulesLift X) :
    (moduleAtObjectLift y).obj ((moduleDirectImageLift f).obj M) ⟶
      (AlgebraicSpace.Modules.pushforwardLift fU).obj ((coefficient f y U eU).obj M) where
  val :=
    { app := underivedAppHom f y U fU eU h_fst M
      naturality := underivedAppHom_naturality f y U fU eU h_fst M }

/-- Naturality of `underivedApp` in the lifted module. -/
theorem underivedApp_naturality ⦃M N : EtaleModulesLift X⦄ (φ : M ⟶ N) :
    (moduleDirectImageLift f ⋙ moduleAtObjectLift y).map φ ≫
        underivedApp f y U fU eU h_fst N =
      underivedApp f y U fU eU h_fst M ≫
        (coefficient f y U eU ⋙ AlgebraicSpace.Modules.pushforwardLift fU).map φ :=
  sorry

/-- The geometric section functions assemble into the canonical comparison square. -/
def underived : moduleDirectImageLift f ⋙ moduleAtObjectLift y ⟶
    coefficient f y U eU ⋙ AlgebraicSpace.Modules.pushforwardLift fU where
  app := underivedApp f y U fU eU h_fst
  naturality := underivedApp_naturality f y U fU eU h_fst

/-- Coefficient restriction is additive. -/
instance coefficient_additive : (coefficient f y U eU).Additive := by unfold coefficient; infer_instance
/-- Coefficient restriction preserves finite limits. -/
instance coefficient_limits : PreservesFiniteLimits (coefficient f y U eU) :=
  sorry
/-- Coefficient restriction preserves finite colimits. -/
instance coefficient_colimits : PreservesFiniteColimits (coefficient f y U eU) :=
  sorry
/-- Restriction at `y` preserves finite limits. -/
instance atObject_limits : PreservesFiniteLimits (moduleAtObjectLift y) :=
  sorry
/-- Restriction at `y` preserves finite colimits. -/
instance atObject_colimits : PreservesFiniteColimits (moduleAtObjectLift y) :=
  sorry

/-- Derive the actual canonical underived square on the explicit lift of original F. -/
def comparison (F : etaleModules X) (i : ℕ) :
    (moduleAtObjectLift y).obj (moduleHigherDirectImageLift f F i) ⟶
      (AlgebraicSpace.Modules.higherDirectImageLift fU i).obj
        ((coefficient f y U eU).obj ((ModuleUniverseComparison.lift X).obj F)) :=
  Functor.RightDerived.exactSquareApp (moduleDirectImageLift f)
    (AlgebraicSpace.Modules.pushforwardLift fU) (coefficient f y U eU) (moduleAtObjectLift y)
    (underived f y U fU eU h_fst) i ((ModuleUniverseComparison.lift X).obj F)


end AlgebraicGeometry.GroupoidsOver.HigherDirectImageComparison
