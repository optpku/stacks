module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Presentation.Derived
public import ReasLib.CategoryTheory.DerivedCategory.Ext
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ext¹ classes of conormal maps on a ringed site

After a polynomial presentation of a homomorphism of sheaves of rings, a map out of the
conormal source determines a class in `Ext⁽1⁾` of the presentation model of the naive
cotangent complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf
open SheafOfModules.RingedSite
open scoped DerivedExt

noncomputable section

universe c v w

namespace SheafOfModules.RingedSite.NaiveCotangent

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{w})]
variable [HasWeakSheafify J CommRingCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [HasSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {A B : Sheaf J CommRingCat.{w}}
variable (φ : A ⟶ B)
variable (G : SheafOfModules (ringSheaf J (Under.mk φ).right))
variable [HasDerivedCategory (SheafOfModules (ringSheaf J (Under.mk φ).right))]

/-- Incoming differentials into degree `-1` of a presentation model vanish after composing with
a map out of the conormal source. -/
theorem ofGenerators_d_comp_conormalHom
    (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk φ))
    (f : (Presentation.ofGenerators E α).X (-1) ⟶ G)
    (i : ℤ) (hi : (ComplexShape.up ℤ).Rel i (-1)) :
    (Presentation.ofGenerators E α).d i (-1) ≫ f = 0 := sorry

/-- The derived `Ext⁽1⁾` class of a `B`-linear map from the conormal source of a polynomial
presentation of `B`. -/
def conormalHomClass
    (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk φ))
    (f : (Presentation.ofGenerators E α).X (-1) ⟶ G) :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (Presentation.ofGenerators E α),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)) :=
  DerivedCategory.Q.map
      (HomologicalComplex.mkHomToSingle f (ofGenerators_d_comp_conormalHom φ G E α f)) ≫
    ((DerivedCategory.singleFunctors _).shiftIso (1 : ℤ) (-1) 0
      (add_neg_cancel (1 : ℤ))).inv.app G

/-- `conormalHomClass` is `DerivedCategory.Q.map` of `HomologicalComplex.mkHomToSingle`, composed
with the canonical identification of `G` in degree `-1` with the shift of `G` in degree `0`. -/
theorem conormalHomClass_def
    (E : Sheaf J (Type w))
    (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk φ))
    (f : (Presentation.ofGenerators E α).X (-1) ⟶ G) :
    conormalHomClass φ G E α f =
      DerivedCategory.Q.map
          (HomologicalComplex.mkHomToSingle f (ofGenerators_d_comp_conormalHom φ G E α f)) ≫
        ((DerivedCategory.singleFunctors _).shiftIso (1 : ℤ) (-1) 0
          (add_neg_cancel (1 : ℤ))).inv.app G := sorry

end SheafOfModules.RingedSite.NaiveCotangent
