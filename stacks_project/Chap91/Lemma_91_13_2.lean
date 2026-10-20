module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Presentation.Ext
import StacksCheckRecall

/-!
# Representing Ext¹ of the naive cotangent complex by a conormal map

On a site, after a locally surjective polynomial presentation, any class in
`Ext⁽1⁾` of the naive cotangent complex is the class of an actual map out of the conormal source.
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

/- Lemma 91.13.2: on a site `C`, any class
`ξ` in `Ext⁽1⁾(DerivedCategory.Q.obj (obj A (Under.mk φ)), DerivedCategory.Q.obj ((singleFunctor 0).obj G))`
is represented, after a locally surjective polynomial presentation
`α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk φ)`, by an actual `B`-linear map
`(Presentation.ofGenerators E α).X (-1) ⟶ G`. -/
@[stacks 08UJ] #check (SheafOfModules.RingedSite.NaiveCotangent.exists_conormalHomClass φ G :
  (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (obj A (Under.mk φ)),
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G))) →
    ∃ (E : Sheaf J (Type w))
      (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk φ)),
      IsLocallySurjective (FreeAlgebra.evaluation (Under.mk φ) E α).right ∧
        ∃ (f : (Presentation.ofGenerators E α).X (-1) ⟶ G),
          Presentation.derivedComparison E α ≫ ξ = conormalHomClass φ G E α f)

end SheafOfModules.RingedSite.NaiveCotangent
