module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.Sections

/-!
# Objectwise sections of the ring-sheaf cotangent complex

The canonical comparison from the sheafified objectwise cotangent complex to the
sheaf cotangent complex is available through the shared sections API.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open Opposite
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.CotangentComplex

noncomputable section

universe u

namespace SheafOfModules.RingedSite.CotangentComplex.Sections

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
variable {A B : Sheaf J CommRingCat.{u}}

#check (SheafOfModules.RingedSite.CotangentComplex.Sections.comparison :
  ∀ {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B),
    SheafOfModules.RingedSite.CotangentComplex.Sections.sheafify φ ⟶
      SheafOfModules.RingedSite.CotangentComplex.obj A (Under.mk φ))

end SheafOfModules.RingedSite.CotangentComplex.Sections
