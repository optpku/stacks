module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.WeakSerre
import StacksCheckRecall

/-!
# Lemma 18.24.4

Flat restriction maps make quasicoherent module sheaves on a chaotic site a weak Serre class.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty
open CategoryTheory.Presheaf
open SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace SheafOfModules

variable {C : Type u} [Category.{v} C]
variable (O : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{w})
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose
  (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasSheafify (⊥ : GrothendieckTopology C)
  AddCommGrpCat.{w}]
variable [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective
  AddCommGrpCat.{w}]
variable [∀ U : C, HasWeakSheafify
  ((⊥ : GrothendieckTopology C).over U) AddCommGrpCat.{w}]
variable [∀ U : C, ((⊥ : GrothendieckTopology C).over U).WEqualsLocallyBijective
  AddCommGrpCat.{w}]
variable [Restriction.Flat O.obj]

/- Lemma 18.24.4 (0GZP): under flat restriction maps, quasicoherent O-modules form a weak
Serre subcategory of all O-module sheaves. -/
@[stacks 0GZP]
#check
  (isQuasicoherent.isWeakSerreClass_of_flat O :
    IsWeakSerreClass
      (isQuasicoherent (ringSheaf (⊥ : GrothendieckTopology C) O)))

end SheafOfModules
