/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap52.Remark_52_6_14_Localization_and_derived_completion
public import stacks_project.Chap52.Lemma_52_6_20
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.OverSections

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open Opposite
open RingedSite.Hom
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.ExtendedCech

noncomputable section

universe u

namespace RingedSite.Hom.ModuleDerived

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}

/-- The local section ring of a ringed site presented by a commutative-ring sheaf retains its
canonical commutative-ring structure. -/
noncomputable instance sectionRingCommRing (U : C) :
    CommRing ((RingedSite.ofCommRingSheaf J O).structureSheaf.obj.obj (op U)) :=
  inferInstanceAs (CommRing (O.obj.obj (op U)))

/-- Evaluate a section of the structure module on the slice over `U` as an element of the
local section ring. -/
noncomputable def sectionGeneratorValue (U : C)
    (s : (unitModule (J.over U) (O.over U)).sections) :
    (RingedSite.ofCommRingSheaf J O).structureSheaf.obj.obj (op U) :=
  SheafOfModules.sectionsOverEquiv (unitModule J O) U s

/-- `sectionGeneratorValue` is terminal evaluation under the slice-section equivalence. -/
theorem sectionGeneratorValue_eq (U : C)
    (s : (unitModule (J.over U) (O.over U)).sections) :
    sectionGeneratorValue U s =
      SheafOfModules.sectionsOverEquiv (unitModule J O) U s := sorry

/-- The ideal generated in `O(U)` by a finite family of sections on the slice over `U` is
finitely generated. -/
theorem sectionGeneratorIdeal_fg (U : C) {r : ℕ}
    (f : Fin r → (unitModule (J.over U) (O.over U)).sections) :
    (Ideal.span (Set.range (fun i ↦ sectionGeneratorValue U (f i)))).FG := sorry

/-- Derived sections of an ideal-sheaf completion target are complete with respect to the
ideal in `O(U)` spanned by the chosen generators. -/
theorem derivedSectionsCompletionTarget_isComplete
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (U : C) {r : ℕ}
    (f : Fin r → (unitModule (J.over U) (O.over U)).sections)
    (hgen : generatedIdeal f = imageSubobject (I.arrow.over U))
    {K Khat : RingedSiteDerived J O} (eta : K ⟶ Khat)
    (heta : IsDerivedCompletion.{u, u, u, u} I eta) :
    DerivedCategory.IsDerivedCompleteWithRespectTo
      ((moduleSectionsDerived (RingedSite.ofCommRingSheaf J O) U).obj Khat)
      (Ideal.span (Set.range (fun i ↦ sectionGeneratorValue U (f i)))) := sorry

/-- The canonical comparison from the derived completion of `RΓ(U, K)` at the ideal spanned
by the chosen generators to `RΓ(U, Khat)`. -/
noncomputable def derivedSectionsCompletionComparison
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (U : C) {r : ℕ}
    (f : Fin r → (unitModule (J.over U) (O.over U)).sections)
    (hgen : generatedIdeal f = imageSubobject (I.arrow.over U))
    {K Khat : RingedSiteDerived J O} (eta : K ⟶ Khat)
    (heta : IsDerivedCompletion.{u, u, u, u} I eta) :
    derivedCompletionOf
      (Ideal.span (Set.range (fun i ↦ sectionGeneratorValue U (f i))))
        (sectionGeneratorIdeal_fg U f)
      ((moduleSectionsDerived (RingedSite.ofCommRingSheaf J O) U).obj K) ⟶
      (moduleSectionsDerived (RingedSite.ofCommRingSheaf J O) U).obj Khat :=
  DerivedCompletion.lift
    (Ideal.span (Set.range (fun i ↦ sectionGeneratorValue U (f i))))
      (sectionGeneratorIdeal_fg U f)
    (derivedSectionsCompletionTarget_isComplete I U f hgen eta heta)
      ((moduleSectionsDerived (RingedSite.ofCommRingSheaf J O) U).map eta)

/-- The completion unit followed by the comparison is the morphism on derived sections induced
by the ideal-sheaf completion map. -/
theorem toDerivedCompletion_comp_derivedSectionsCompletionComparison
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (U : C) {r : ℕ}
    (f : Fin r → (unitModule (J.over U) (O.over U)).sections)
    (hgen : generatedIdeal f = imageSubobject (I.arrow.over U))
    {K Khat : RingedSiteDerived J O} (eta : K ⟶ Khat)
    (heta : IsDerivedCompletion.{u, u, u, u} I eta) :
    toDerivedCompletion
      (Ideal.span (Set.range (fun i ↦ sectionGeneratorValue U (f i))))
        (sectionGeneratorIdeal_fg U f)
      ((moduleSectionsDerived (RingedSite.ofCommRingSheaf J O) U).obj K) ≫
      derivedSectionsCompletionComparison I U f hgen eta heta =
        (moduleSectionsDerived (RingedSite.ofCommRingSheaf J O) U).map eta := sorry

/-- Remark 52.6.21: the canonical comparison from the derived completion of `RΓ(U, K)` with
respect to the ideal spanned by the chosen generators to `RΓ(U, Khat)` is an isomorphism. -/
@[stacks 0CQI, instance]
noncomputable instance derivedSectionsCompletionComparisonIsIso
    (I : Subobject (unitModule J O))
    [(I : ringedSiteModuleCategory J O).IsFiniteType]
    (U : C) {r : ℕ}
    (f : Fin r → (unitModule (J.over U) (O.over U)).sections)
    (hgen : generatedIdeal f = imageSubobject (I.arrow.over U))
    {K Khat : RingedSiteDerived J O} (eta : K ⟶ Khat)
    (heta : IsDerivedCompletion.{u, u, u, u} I eta) :
    IsIso (derivedSectionsCompletionComparison I U f hgen eta heta) := sorry

end RingedSite.Hom.ModuleDerived
