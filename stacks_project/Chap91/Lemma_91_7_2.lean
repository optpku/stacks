module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Presentation.Derived
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Tactic.CrossRefAttribute

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
variable [HasDerivedCategory (SheafOfModules (ringSheaf (Opens.grothendieckTopology X) B.right))]

/-- Incoming differentials into degree `-1` of a presentation model vanish after composing with
a map out of the conormal source. -/
theorem ofGenerators_d_comp_conormalHom
    (E : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
    (α : E ⟶ FreeAlgebra.Presentation.generators B)
    (f : (Presentation.ofGenerators E α).X (-1) ⟶ G)
    (i : ℤ) (hi : (ComplexShape.up ℤ).Rel i (-1)) :
    (Presentation.ofGenerators E α).d i (-1) ≫ f = 0 := sorry

/-- The derived `Ext⁽1⁾` class of a `B`-linear map from the conormal source of a polynomial
presentation of `B`. -/
def conormalHomClass
    (E : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
    (α : E ⟶ FreeAlgebra.Presentation.generators B)
    (f : (Presentation.ofGenerators E α).X (-1) ⟶ G) :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (Presentation.ofGenerators E α),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)) :=
  DerivedCategory.Q.map
      (HomologicalComplex.mkHomToSingle f (ofGenerators_d_comp_conormalHom G E α f)) ≫
    ((DerivedCategory.singleFunctors _).shiftIso (1 : ℤ) (-1) 0
      (add_neg_cancel (1 : ℤ))).inv.app G

/-- `conormalHomClass` is `DerivedCategory.Q.map` of `HomologicalComplex.mkHomToSingle`, composed
with the canonical identification of `G` in degree `-1` with the shift of `G` in degree `0`. -/
theorem conormalHomClass_def
    (E : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
    (α : E ⟶ FreeAlgebra.Presentation.generators B)
    (f : (Presentation.ofGenerators E α).X (-1) ⟶ G) :
    conormalHomClass G E α f =
      DerivedCategory.Q.map
          (HomologicalComplex.mkHomToSingle f (ofGenerators_d_comp_conormalHom G E α f)) ≫
        ((DerivedCategory.singleFunctors _).shiftIso (1 : ℤ) (-1) 0
          (add_neg_cancel (1 : ℤ))).inv.app G := sorry

/-- Lemma 91.7.2: on a topological space `X`, any class `ξ` in
`Ext⁽1⁾(DerivedCategory.Q.obj (obj A B), DerivedCategory.Q.obj ((singleFunctor 0).obj G))`
is represented, after a locally surjective polynomial presentation
`α : E ⟶ FreeAlgebra.Presentation.generators B`, by an actual map
`(Presentation.ofGenerators E α).X (-1) ⟶ G`. -/
@[stacks 08UB]
theorem exists_conormalHomClass
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (obj A B),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G))) :
    ∃ (E : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u))
      (α : E ⟶ FreeAlgebra.Presentation.generators B),
      IsLocallySurjective (FreeAlgebra.evaluation B E α).right ∧
        ∃ (f : (Presentation.ofGenerators E α).X (-1) ⟶ G),
          Presentation.derivedComparison E α ≫ ξ = conormalHomClass G E α f := sorry

end TopCat.Sheaf.NaiveCotangent
