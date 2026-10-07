module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Chaotic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Weak Serre closure of quasicoherent modules on a chaotic site

The reusable weak Serre theorem is first established for the presheaf-owned base-change
compatibility property.  The chaotic quasicoherence criterion transports it to Mathlib's
quasicoherent object property.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty
open CategoryTheory.Presheaf
open SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace SheafOfModules.isQuasicoherent

variable {C : Type u} [Category.{v} C]
variable (O : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{w})
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose
  (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{w}]
variable [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : C, HasWeakSheafify
  ((⊥ : GrothendieckTopology C).over U) AddCommGrpCat.{w}]
variable [∀ U : C, ((⊥ : GrothendieckTopology C).over U).WEqualsLocallyBijective
  AddCommGrpCat.{w}]

/-- Lemma 18.24.4 (0GZP): if the coefficient presheaf has flat restriction maps, then
quasicoherent module sheaves on the chaotic site form a weak Serre class. -/
@[stacks 0GZP]
theorem isWeakSerreClass_of_flat [Restriction.Flat O.obj] :
    IsWeakSerreClass
      (SheafOfModules.isQuasicoherent
        (ringSheaf (⊥ : GrothendieckTopology C) O)) := sorry

attribute [instance] isWeakSerreClass_of_flat

end SheafOfModules.isQuasicoherent
