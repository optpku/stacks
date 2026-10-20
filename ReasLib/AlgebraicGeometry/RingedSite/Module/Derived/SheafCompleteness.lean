module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Completeness
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ConstantCompletion
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import ReasLib.CategoryTheory.Sites.WeaklyContractible.Enough

/-!
# Derived-complete sheaves of constant Noetherian coefficients

Degree-zero derived completeness, adic comparison maps, and closure properties
on sites with enough weakly contractible objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty
open SheafOfModules.RingedSite SheafOfModules.RingedSite.IdealSheaf
open RingedSite.Hom.ModuleDerived.ConstantCompletion

noncomputable section

universe u

namespace RingedSite.Hom.ModuleDerived

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable (I : Ideal Λ)

/-- A sheaf of `Λ`-modules is derived complete with respect to `I` when its
degree-zero derived object is complete with respect to the constant ideal sheaf. -/
abbrev isDerivedCompleteSheaf
    (F : ringedSiteModuleCategory J (constantRingSheaf J Λ)) : Prop :=
  IsDerivedCompleteWithRespectTo
    ((DerivedCategory.singleFunctor
        (ringedSiteModuleCategory J (constantRingSheaf J Λ)) (0 : ℤ)).obj F)
    (constantIdealSheaf J I)

/-- Derived completeness of a sheaf is derived completeness of its degree-zero object. -/
theorem isDerivedCompleteSheaf_iff
    (F : ringedSiteModuleCategory J (constantRingSheaf J Λ)) :
    isDerivedCompleteSheaf J I F ↔
      IsDerivedCompleteWithRespectTo
        ((DerivedCategory.singleFunctor
            (ringedSiteModuleCategory J (constantRingSheaf J Λ)) (0 : ℤ)).obj F)
        (constantIdealSheaf J I) := sorry

/-- The object property selecting derived-complete sheaves of `Λ`-modules. -/
abbrev derivedCompleteSheafProperty :
    ObjectProperty (ringedSiteModuleCategory J (constantRingSheaf J Λ)) :=
  fun F ↦ isDerivedCompleteSheaf J I F

/-- Membership in the derived-complete object property is derived completeness. -/
theorem derivedCompleteSheafProperty_apply
    (F : ringedSiteModuleCategory J (constantRingSheaf J Λ)) :
    derivedCompleteSheafProperty J I F ↔ isDerivedCompleteSheaf J I F := sorry

/-- The canonical projections to successive ideal-power quotients are compatible
with the quotient transition maps. -/
theorem adicCompletionCone_naturality
    (F : ringedSiteModuleCategory J (constantRingSheaf J Λ)) (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj F).map (homOfLE (n.le_add_right 1)).op ≫
        PowerQuotientModule.projection (constantIdealSheaf J I) F n =
      PowerQuotientModule.projection (constantIdealSheaf J I) F (n + 1) ≫
        (PowerQuotientModule.system (constantIdealSheaf J I) F).map
          (homOfLE (n.le_add_right 1)).op := sorry

/-- The cone of canonical projections from `F` to its ideal-power quotients. -/
def adicCompletionCone
    (F : ringedSiteModuleCategory J (constantRingSheaf J Λ)) :
    Cone (PowerQuotientModule.system (constantIdealSheaf J I) F) where
  pt := F
  π := NatTrans.ofOpSequence
    (fun n ↦ PowerQuotientModule.projection (constantIdealSheaf J I) F n)
    (fun n ↦ adicCompletionCone_naturality J I F n)

/-- The `n`th leg of the adic cone is the canonical quotient projection. -/
theorem adicCompletionCone_π
    (F : ringedSiteModuleCategory J (constantRingSheaf J Λ)) (n : ℕ) :
    (adicCompletionCone J I F).π.app (op n) =
      PowerQuotientModule.projection (constantIdealSheaf J I) F n := sorry

/-- The canonical comparison from a sheaf to the limit of its ideal-power quotients. -/
def toAdicLimit
    (F : ringedSiteModuleCategory J (constantRingSheaf J Λ)) :
    F ⟶ limit (PowerQuotientModule.system (constantIdealSheaf J I) F) :=
  limit.lift (PowerQuotientModule.system (constantIdealSheaf J I) F)
    (adicCompletionCone J I F)

/-- The adic comparison projects to the canonical quotient map at every stage. -/
theorem toAdicLimit_comp_π
    (F : ringedSiteModuleCategory J (constantRingSheaf J Λ)) (n : ℕ) :
    toAdicLimit J I F ≫
        limit.π (PowerQuotientModule.system (constantIdealSheaf J I) F) (op n) =
      PowerQuotientModule.projection (constantIdealSheaf J I) F n := sorry

/-- The completed constant unit module, as the limit of its ideal-power quotients. -/
def completedUnitModule :
    ringedSiteModuleCategory J (constantRingSheaf J Λ) :=
  limit (PowerQuotientModule.system (constantIdealSheaf J I)
    (unitModule J (constantRingSheaf J Λ)))

/-- The completed unit module is the inverse limit of the unit-module power quotients. -/
theorem completedUnitModule_def :
    completedUnitModule J I =
      limit (PowerQuotientModule.system (constantIdealSheaf J I)
        (unitModule J (constantRingSheaf J Λ))) := sorry

/-- Derived-complete module sheaves form a weak Serre class on a site with enough
weakly contractible objects. -/
theorem derivedCompleteSheaf_isWeakSerreClass
    (hEnough : J.HasEnoughObjectsWithProperty J.IsWeaklyContractible) :
    IsWeakSerreClass (derivedCompleteSheafProperty J I) := sorry

/-- The adic comparison is an isomorphism exactly when the sheaf is derived complete
and the intersection of its ideal-power submodules, the comparison kernel, is zero. -/
theorem isIso_toAdicLimit_iff
    (hEnough : J.HasEnoughObjectsWithProperty J.IsWeaklyContractible)
    (F : ringedSiteModuleCategory J (constantRingSheaf J Λ)) :
    IsIso (toAdicLimit J I F) ↔
      isDerivedCompleteSheaf J I F ∧ IsZero (kernel (toAdicLimit J I F)) := sorry

/-- The completed constant unit module is derived complete on a site with enough
weakly contractible objects. -/
theorem completedUnitModule_isDerivedCompleteSheaf
    (hEnough : J.HasEnoughObjectsWithProperty J.IsWeaklyContractible) :
    isDerivedCompleteSheaf J I (completedUnitModule J I) := sorry

/-- Sequential inverse limits of derived-complete module sheaves are derived complete
on a site with enough weakly contractible objects. -/
theorem limit_isDerivedCompleteSheaf
    (hEnough : J.HasEnoughObjectsWithProperty J.IsWeaklyContractible)
    (Fsys : SequentialInverseSystem
      (ringedSiteModuleCategory J (constantRingSheaf J Λ)))
    (hF : ∀ n, isDerivedCompleteSheaf J I (Fsys.obj (op n))) :
    isDerivedCompleteSheaf J I (limit Fsys) := sorry

/-- A derived object is complete exactly when every cohomology sheaf is complete,
on a site with enough weakly contractible objects. -/
theorem isDerivedComplete_iff_cohomologySheaf
    (hEnough : J.HasEnoughObjectsWithProperty J.IsWeaklyContractible)
    (K : RingedSiteDerived.{u, u, u, u} J (constantRingSheaf J Λ)) :
    IsDerivedCompleteWithRespectTo.{u, u, u, u} K (constantIdealSheaf J I) ↔
      DerivedCategory.cohomologyIn (derivedCompleteSheafProperty J I) K := sorry

end RingedSite.Hom.ModuleDerived
