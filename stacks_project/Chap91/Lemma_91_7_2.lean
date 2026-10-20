/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Presentation.Ext
public import Mathlib.Topology.Sheaves.Sheaf
import StacksCheckRecall

/-!
# Representing Ext¹ of the naive cotangent complex by a conormal map

On a topological space, after a locally surjective polynomial presentation, any class in
`Ext⁽1⁾` of the naive cotangent complex is the class of an actual map out of the conormal source.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf TopologicalSpace
open SheafOfModules.RingedSite
open scoped DerivedExt

noncomputable section

universe u

namespace TopCat.Sheaf.NaiveCotangent

open SheafOfModules.RingedSite.NaiveCotangent

variable {X : TopCat.{u}}
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable {A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
variable {B : Under A}
variable (G : SheafOfModules (ringSheaf (Opens.grothendieckTopology X) B.right))
variable [derivedCategory :
  HasDerivedCategory (SheafOfModules (ringSheaf (Opens.grothendieckTopology X) B.right))]

/-- The derived `Ext⁽1⁾` class of a `B`-linear map from the conormal source of a polynomial
presentation of `B`. -/
def conormalHomClass
    (E : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
    (α : E ⟶ FreeAlgebra.Presentation.generators B)
    (f : (Presentation.ofGenerators E α).X (-1) ⟶ G) :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (Presentation.ofGenerators E α),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)) :=
  SheafOfModules.RingedSite.NaiveCotangent.conormalHomClass
    (derivedCategory := derivedCategory) B.hom G E α f

/-- Lemma 91.7.2: on a topological space `X`, any class `ξ` in
`Ext⁽1⁾(DerivedCategory.Q.obj (obj A B), DerivedCategory.Q.obj ((singleFunctor 0).obj G))`
is represented, after a locally surjective polynomial presentation
`α : E ⟶ FreeAlgebra.Presentation.generators B`, by an actual map
`(Presentation.ofGenerators E α).X (-1) ⟶ G`. -/
theorem exists_conormalHomClass
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (obj A B),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G))) :
    ∃ (E : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
      (α : E ⟶ FreeAlgebra.Presentation.generators B),
      IsLocallySurjective (FreeAlgebra.evaluation B E α).right ∧
        ∃ (f : (Presentation.ofGenerators E α).X (-1) ⟶ G),
          Presentation.derivedComparison E α ≫ ξ = conormalHomClass G E α f :=
  SheafOfModules.RingedSite.NaiveCotangent.exists_conormalHomClass
    (derivedCategory := derivedCategory) B.hom G ξ

/- Lemma 91.7.2: every derived extension class of the naive cotangent complex is represented,
after a locally surjective polynomial presentation, by a map from the conormal source. -/
@[stacks 08UB] #check (SheafOfModules.RingedSite.NaiveCotangent.exists_conormalHomClass
  (derivedCategory := derivedCategory) B.hom G :
  (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (obj A B),
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G))) →
    ∃ (E : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
      (α : E ⟶ FreeAlgebra.Presentation.generators B),
      IsLocallySurjective (FreeAlgebra.evaluation B E α).right ∧
        ∃ (f : (Presentation.ofGenerators E α).X (-1) ⟶ G),
          Presentation.derivedComparison E α ≫ ξ =
            SheafOfModules.RingedSite.NaiveCotangent.conormalHomClass
              (derivedCategory := derivedCategory) B.hom G E α f)

end TopCat.Sheaf.NaiveCotangent
