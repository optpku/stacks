module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.InternalHom.Bifunctor
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed.Shift
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.IntMonoidal
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor

/-!
# Actual shifts and triangles of derived sheaf internal Hom

The concrete cochain shift matrices are transported through actual K-injective model maps and
the existing model comparison. No monoidal or closed structure on the derived category is an
input. Source shifts use the negative shift prescribed by its triangulated opposite category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules.RingedSite SheafOfModules.RingedSite.RingedSiteDerived
open scoped Pretriangulated.Opposite

noncomputable section

universe u v

namespace RingedSite.Hom.ModuleDerived.InternalHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O : Sheaf J CommRingCat.{max u v}}

/-- The actual target shift comparison on the strict sheaf-Hom complexes. -/
def strictTargetShiftIso (F I : CochainComplex (ringedSiteModuleCategory J O) ℤ) (n : ℤ) :
    (strictInternalHom.obj (op F)).obj (I⟦n⟧) ≅
      ((strictInternalHom.obj (op F)).obj I)⟦n⟧ :=
  CochainComplex.InternalHom.targetShiftIso F I n

/-- The actual normalized negative-source shift comparison on strict sheaf-Hom complexes. -/
def strictSourceShiftIso (F I : CochainComplex (ringedSiteModuleCategory J O) ℤ) (n : ℤ) :
    (strictInternalHom.obj (op (F⟦-n⟧))).obj I ≅
      ((strictInternalHom.obj (op F)).obj I)⟦n⟧ :=
  CochainComplex.InternalHom.sourceShiftIso F I n

/-- Lift the canonical derived shift of a model to an actual cochain comparison with the
selected K-injective model of the shifted object. -/
def modelShiftMap (N : max J O) (n : ℤ) :
    (injectiveModel N)⟦n⟧ ⟶ injectiveModel (N⟦n⟧) :=
  liftToInjectiveModel ((injectiveModel N)⟦n⟧) (N⟦n⟧)
    ((Functor.commShiftIso
      (DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ max J O) n).hom.app
        (injectiveModel N) ≫
      (shiftFunctor (max J O) n).map (injectiveModelIso N).hom)

/-- The model-shift comparison has its displayed canonical isomorphism as derived image. -/
instance modelShiftMap_quasiIso (N : max J O) (n : ℤ) :
    QuasiIso (modelShiftMap N n) := sorry

/-- Actual postcomposition by the target model-shift comparison. -/
def targetModelShiftMap (M N : max J O) (n : ℤ) :
    objOfModels (injectiveModel M) ((injectiveModel N)⟦n⟧) ⟶
      objOfModels (injectiveModel M) (injectiveModel (N⟦n⟧)) :=
  DerivedCategory.Q.map
    ((strictInternalHom.obj (op (injectiveModel M))).map (modelShiftMap N n))

/-- A quasi-isomorphism between K-injective targets is a homotopy equivalence, so this
actual postcomposition map is invertible after passing to the derived category. -/
instance targetModelShiftMap_isIso (M N : max J O) (n : ℤ) :
    IsIso (targetModelShiftMap M N n) := sorry

/-- Actual precomposition by the negative-source model-shift comparison. -/
def sourceModelShiftMap (M N : max J O) (n : ℤ) :
    objOfModels (injectiveModel (M⟦-n⟧)) (injectiveModel N) ⟶
      objOfModels ((injectiveModel M)⟦-n⟧) (injectiveModel N) :=
  DerivedCategory.Q.map
    ((strictInternalHom.map (modelShiftMap M (-n)).op).app (injectiveModel N))

/-- The actual source-model shift comparison is a homotopy equivalence between K-injective
complexes, and precomposition preserves that equivalence. -/
instance sourceModelShiftMap_isIso (M N : max J O) (n : ℤ) :
    IsIso (sourceModelShiftMap M N n) := sorry

/-- The target-variable derived shift comparison, with all maps fixed by actual cochain
postcomposition, strict shift matrices and derived localization. -/
def targetShiftIso (M N : max J O) (n : ℤ) :
    obj M (N⟦n⟧) ≅ (obj M N)⟦n⟧ :=
  (modelComparisonIso M (N⟦n⟧)).symm ≪≫
    (asIso (targetModelShiftMap M N n)).symm ≪≫
    DerivedCategory.Q.mapIso
      (strictTargetShiftIso (injectiveModel M) (injectiveModel N) n) ≪≫
    (Functor.commShiftIso
      (DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ max J O) n).app
        ((strictInternalHom.obj (op (injectiveModel M))).obj (injectiveModel N)) ≪≫
    (shiftFunctor (max J O) n).mapIso (modelComparisonIso M N)

/-- The source-variable derived shift comparison, using negative source shift and the
coherent sign normalization of the strict cochain Hom. -/
def sourceShiftIso (M N : max J O) (n : ℤ) :
    obj (M⟦-n⟧) N ≅ (obj M N)⟦n⟧ :=
  (modelComparisonIso (M⟦-n⟧) N).symm ≪≫
    asIso (sourceModelShiftMap M N n) ≪≫
    DerivedCategory.Q.mapIso
      (strictSourceShiftIso (injectiveModel M) (injectiveModel N) n) ≪≫
    (Functor.commShiftIso
      (DerivedCategory.Q : CochainComplex (ringedSiteModuleCategory J O) ℤ ⥤ max J O) n).app
        ((strictInternalHom.obj (op (injectiveModel M))).obj (injectiveModel N)) ≪≫
    (shiftFunctor (max J O) n).mapIso (modelComparisonIso M N)

/-- The natural target-variable shift comparison of the actual derived sheaf-Hom functor. -/
def targetCommShiftIso (M : max J O) (n : ℤ) :
    shiftFunctor (max J O) n ⋙ targetFunctor M ≅
      targetFunctor M ⋙ shiftFunctor (max J O) n :=
  NatIso.ofComponents (fun N ↦ targetShiftIso M N n) (by intro N N' f; sorry)

/-- The natural source-variable comparison respects the opposite category's negative shift. -/
def sourceCommShiftIso (N : max J O) (n : ℤ) :
    shiftFunctor (max J O)ᵒᵖ n ⋙ sourceFunctor N ≅
      sourceFunctor N ⋙ shiftFunctor (max J O) n :=
  Functor.isoWhiskerRight
      (Pretriangulated.shiftFunctorOpIso (max J O) n (-n) (add_neg_cancel n))
      (sourceFunctor N) ≪≫
    NatIso.ofComponents (fun M ↦ sourceShiftIso M.unop N n) (by intro M M' f; sorry)

/-- The actual target-variable derived sheaf-Hom functor commutes coherently with shifts. -/
@[stacks 08JC "canonical sheaf-valued target-variable shift compatibility"]
instance targetFunctor_commShift (M : max J O) : (targetFunctor M).CommShift ℤ where
  commShiftIso := targetCommShiftIso M
  commShiftIso_zero := sorry
  commShiftIso_add := sorry

/-- The actual contravariant source-variable derived sheaf-Hom functor commutes with shifts. -/
@[stacks 08JC "canonical sheaf-valued source-variable shift compatibility"]
instance sourceFunctor_commShift (N : max J O) : (sourceFunctor N).CommShift ℤ where
  commShiftIso := sourceCommShiftIso N
  commShiftIso_zero := sorry
  commShiftIso_add := sorry

/-- Termwise split short exact sequences in the target variable induce distinguished
triangles under the actual derived sheaf-Hom construction. -/
@[stacks 08JC "canonical sheaf-valued target-variable triangulated functor"]
instance targetFunctor_isTriangulated (M : max J O) :
    (targetFunctor M).IsTriangulated := sorry

/-- Termwise split short exact sequences in the source variable induce distinguished
triangles under the actual contravariant derived sheaf-Hom construction. -/
@[stacks 08JC "canonical sheaf-valued source-variable triangulated functor"]
instance sourceFunctor_isTriangulated (N : max J O) :
    (sourceFunctor N).IsTriangulated := sorry

end RingedSite.Hom.ModuleDerived.InternalHom
