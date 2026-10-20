module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Presentation.Ext

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

/- The conormal class is owned by the derived presentation API. -/
#check (SheafOfModules.RingedSite.NaiveCotangent.conormalHomClass φ G :
  (E : Sheaf J (Type w)) →
  (α : E ⟶ FreeAlgebra.Presentation.generators (Under.mk φ)) →
  (f : (Presentation.ofGenerators E α).X (-1) ⟶ G) →
  Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (Presentation.ofGenerators E α),
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)))

end SheafOfModules.RingedSite.NaiveCotangent
