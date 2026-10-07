module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh

/-!
# Coherent cohomology of derived internal Hom on algebraic spaces

On a locally Noetherian algebraic space, derived internal Hom from an object with
bounded-above coherent cohomology to an object with bounded-below coherent cohomology
has bounded-below coherent cohomology.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open CategoryTheory
open CategoryTheory.MonoidalClosed
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable [IsLocallyNoetherian X] [MonoidalCategory (ModuleDerived X)]
variable (H : MonoidalClosed (ModuleDerived X)) (K L : ModuleDerived X)

/-- On a locally Noetherian algebraic space, derived internal Hom from an object with
bounded-above coherent cohomology to an object with bounded-below coherent cohomology has
bounded-below coherent cohomology. -/
theorem boundedBelowCoherentCohomology
    (hK_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X)) K)
    (hK_boundedAbove :
      (t.minus : ObjectProperty (ModuleDerived X)) K)
    (hL_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X)) L)
    (hL_boundedBelow :
      (t.plus : ObjectProperty (ModuleDerived X)) L) :
    DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent (structureSheaf X))
        ((ihomOf H K).obj L) ∧
      (t.plus : ObjectProperty (ModuleDerived X))
        ((ihomOf H K).obj L) := sorry

/-- Derived internal Hom of a bounded-above coherent object into a bounded-below coherent
object has coherent cohomology. -/
theorem boundedBelowCoherentCohomology_cohomologyIn
    (hK_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X)) K)
    (hK_boundedAbove :
      (t.minus : ObjectProperty (ModuleDerived X)) K)
    (hL_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X)) L)
    (hL_boundedBelow :
      (t.plus : ObjectProperty (ModuleDerived X)) L) :
    DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X))
      ((ihomOf H K).obj L) := sorry

/-- Derived internal Hom of a bounded-above coherent object into a bounded-below coherent
object is cohomologically bounded below. -/
theorem boundedBelowCoherentCohomology_plus
    (hK_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X)) K)
    (hK_boundedAbove :
      (t.minus : ObjectProperty (ModuleDerived X)) K)
    (hL_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X)) L)
    (hL_boundedBelow :
      (t.plus : ObjectProperty (ModuleDerived X)) L) :
    (t.plus : ObjectProperty (ModuleDerived X)) ((ihomOf H K).obj L) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom
