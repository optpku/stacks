/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import stacks_project.Chap85.Lemma_85_28_1_Ringed

/-!
# Quasi-coherent modules on the Zariski site of a simplicial scheme

A quasi-coherent module on `U_Zar` is a module sheaf on `zariskiRingedSite U` that is
quasi-coherent in the sense of `SheafOfModules.IsQuasicoherent`. The category of such
sheaves is the corresponding full subcategory `QCoh`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.SimplicialObject

variable (U : SimplicialObject Scheme.{u})

/-- Abelian-group-valued sheaf composition exists on every slice of the Zariski
ringed site of a simplicial scheme. -/
instance hasSheafCompose_zariskiRingedSite_over :
    ∀ x, ((zariskiRingedSite U).siteTopology.over x).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  sorry

/-- Weak sheafification of abelian groups exists on every slice of the Zariski
ringed site of a simplicial scheme. -/
instance hasWeakSheafify_zariskiRingedSite_over :
    ∀ x, HasWeakSheafify ((zariskiRingedSite U).siteTopology.over x)
      AddCommGrpCat.{u} :=
  sorry

/-- Sheafification equivalences on slices of the Zariski ringed site of a
simplicial scheme are exactly the locally bijective morphisms. -/
instance wEqualsLocallyBijective_zariskiRingedSite_over :
    ∀ x, ((zariskiRingedSite U).siteTopology.over x).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  sorry

/-- The object property of quasi-coherent module sheaves on `U_Zar`. -/
abbrev quasiCoherentModuleProperty :
    ObjectProperty (RingedSite.ModuleCat.{u} (zariskiRingedSite U)) :=
  SheafOfModules.isQuasicoherent (zariskiRingedSite U).structureSheaf

/-- `quasiCoherentModuleProperty U` is mathlib's quasi-coherence predicate on
the structure sheaf of the Zariski ringed site. -/
theorem quasiCoherentModuleProperty_eq :
    quasiCoherentModuleProperty U =
      SheafOfModules.isQuasicoherent (zariskiRingedSite U).structureSheaf :=
  sorry

/-- A module sheaf on `U_Zar` lies in `quasiCoherentModuleProperty U` if and only
if it is quasi-coherent. -/
theorem mem_QCoh_iff {M : RingedSite.ModuleCat.{u} (zariskiRingedSite U)} :
    quasiCoherentModuleProperty U M ↔ M.IsQuasicoherent :=
  sorry

/-- The category of quasi-coherent modules on the Zariski ringed site of a
simplicial scheme. -/
abbrev QCoh :=
  (quasiCoherentModuleProperty U).FullSubcategory

namespace QCoh

/-- The inclusion of quasi-coherent modules into all module sheaves on the Zariski
ringed site of `U`. -/
abbrev inclusion : QCoh U ⥤ RingedSite.ModuleCat.{u} (zariskiRingedSite U) :=
  (quasiCoherentModuleProperty U).ι

end QCoh

end AlgebraicGeometry.SimplicialObject
