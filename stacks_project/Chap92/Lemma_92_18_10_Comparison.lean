module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.NaiveComparison

/-!
# Comparison of the cotangent complex with the naive cotangent complex

The canonical comparison and its good-truncation property are available for a commutative
algebra sheaf over an arbitrary small site.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open Opposite
open AlgebraicTopology
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.CotangentComplex
open SheafOfModules.RingedSite.NaiveCotangent.Presentation
  renaming Hom → PresentationHom
open scoped Simplicial ZeroObject

noncomputable section

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]

variable (A : Sheaf J CommRingCat.{u}) (B : Under A)

#check (SheafOfModules.RingedSite.CotangentComplex.toNaive A B :
  SheafOfModules.RingedSite.CotangentComplex.obj A B ⟶ NaiveCotangent.obj A B)

#check (SheafOfModules.RingedSite.CotangentComplex.toNaive_truncGE_quasiIso A B :
  QuasiIso (CochainComplex.truncGEMap
    (SheafOfModules.RingedSite.CotangentComplex.toNaive A B) (-1)))

end
end
