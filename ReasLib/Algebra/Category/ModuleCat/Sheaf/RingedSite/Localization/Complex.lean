module

public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Functor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Exact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Localization.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Complex.Monoidal
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization of complexes of module sheaves

The ordinary localization adjunction acts termwise on unbounded cochain complexes.  Its
restriction functor is strong monoidal, its lower shriek is the induced oplax-monoidal left
adjoint, and the lifted adjunction satisfies the projection formula.  These are the coherent
ambient structures used by differential graded localization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.Localization

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{w}) (U : C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable [(restriction O U : SheafOfModules.{w} (ringSheaf J O) ⥤
  SheafOfModules.{w} ((ringSheaf J O).over U)).IsRightAdjoint]

/-- Restriction to `C / U`, applied termwise to unbounded cochain complexes. -/
@[stacks 0FRV "restriction of complexes to a localization"]
noncomputable def restrictionComplex :
    CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ ⥤
      CochainComplex
        (ringedSiteModuleCategory.{max u v, v, w, w} (J.over U) (O.over U)) ℤ :=
  (restriction O U : SheafOfModules.{w} (ringSheaf J O) ⥤
    SheafOfModules.{w} ((ringSheaf J O).over U)).mapHomologicalComplex (up ℤ)

/-- Extension from `C / U` is additive; equivalently, its degreewise action defines a functor
on cochain complexes. -/
@[stacks 0FRV "additivity of localized extension", instance]
theorem lowerShriek_additive :
    (lowerShriek O U : SheafOfModules.{w} ((ringSheaf J O).over U) ⥤
      SheafOfModules.{w} (ringSheaf J O)).Additive := sorry

/-- Extension from `C / U`, applied termwise to unbounded cochain complexes. -/
@[stacks 0FRV "extension by zero of complexes"]
noncomputable def lowerShriekComplex :
    CochainComplex
        (ringedSiteModuleCategory.{max u v, v, w, w} (J.over U) (O.over U)) ℤ ⥤
      CochainComplex (ringedSiteModuleCategory.{u, v, w, w} J O) ℤ :=
  (lowerShriek O U : SheafOfModules.{w} ((ringSheaf J O).over U) ⥤
    SheafOfModules.{w} (ringSheaf J O)).mapHomologicalComplex (up ℤ)

/-- The ordinary localization adjunction lifted termwise to unbounded cochain complexes. -/
@[stacks 0FRV "localization adjunction on complexes"]
noncomputable def complexAdjunction :
    lowerShriekComplex O U ⊣ restrictionComplex O U :=
  Adjunction.mapHomologicalComplexAdjunction
    (lowerShriekRestrictionAdj O U) (up ℤ)

/-- The tensor comparison for termwise restriction of unbounded complexes is invertible. -/
@[stacks 0FRV "localized complex restriction preserves tensor products", instance]
theorem restrictionComplex_tensorComparison_isIso
    (K L : CochainComplex (SheafOfModules.{w} (ringSheaf J O)) ℤ) :
    IsIso (@Functor.Cochain.tensorComparison _ _ _ _ _ _ _ _ _ _ _ _
      (restriction O U : SheafOfModules.{w} (ringSheaf J O) ⥤
        SheafOfModules.{w} ((ringSheaf J O).over U)) _
      (restrictionMonoidal O U) K L _ _ _) := sorry

/-- Termwise restriction of unbounded complexes is canonically strong monoidal. -/
@[stacks 0FRV "strong-monoidal restriction of complexes", implicit_reducible]
noncomputable instance restrictionComplexMonoidal :
    (restrictionComplex O U).Monoidal :=
  (@Functor.Cochain.coreMonoidal _ _ _ _ _ _ _ _ _ _ _ _
    (restriction O U : SheafOfModules.{w} (ringSheaf J O) ⥤
      SheafOfModules.{w} ((ringSheaf J O).over U)) _
    (restrictionMonoidal O U) _ _ _ _ _ _ _ _ _
    (fun K L ↦ restrictionComplex_tensorComparison_isIso O U K L)).toMonoidal

/-- The lax half of the canonical strong-monoidal structure on complex restriction.  Registering
this projection separately lets APIs requiring only `LaxMonoidal` recover the coherent structure
without a local instance pin. -/
@[stacks 0FRV "lax-monoidal restriction of complexes", implicit_reducible]
noncomputable instance restrictionComplexLaxMonoidal :
    (restrictionComplex O U).LaxMonoidal :=
  (restrictionComplexMonoidal O U).toLaxMonoidal

/-- The canonical oplax-monoidal structure on complex lower shriek transferred from its
strong-monoidal right adjoint. -/
@[stacks 0FRV "oplax-monoidal extension by zero of complexes", implicit_reducible]
noncomputable instance lowerShriekComplexOplaxMonoidal :
    (lowerShriekComplex O U).OplaxMonoidal :=
  (complexAdjunction O U).leftAdjointOplaxMonoidal

/-- The complex localization adjunction is compatible with the transferred monoidal
structures. -/
@[stacks 0FRV "monoidal localization adjunction on complexes", instance]
theorem complexAdjunction_isMonoidal : (complexAdjunction O U).IsMonoidal := sorry

/-- Extension by zero and restriction of unbounded complexes satisfy the projection formula. -/
@[stacks 0FRV "projection formula for localization of complexes", instance]
theorem complexAdjunction_projectionFormula :
    (complexAdjunction O U).ProjectionFormulaMap := sorry

end SheafOfModules.RingedSite.Localization

end
