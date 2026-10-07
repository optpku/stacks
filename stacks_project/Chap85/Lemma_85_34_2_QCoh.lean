module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import stacks_project.Chap85.Lemma_85_34_1_Ringed

/-!
# Quasi-coherent modules on the spaces-étale total site

A quasi-coherent module on `U_spaces,étale` is a module sheaf on
`etaleTotalRingedSite U` that is quasi-coherent in the sense of
`SheafOfModules.IsQuasicoherent`. The category of such sheaves is the
corresponding full subcategory `QCoh`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S))

/-- Abelian-group-valued sheaf composition exists on every slice of the spaces-étale
total ringed site of a simplicial algebraic space. -/
instance hasSheafCompose_etaleTotalRingedSite_over :
    ∀ x, ((etaleTotalRingedSite U).siteTopology.over x).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  sorry

/-- Weak sheafification of abelian groups exists on every slice of the spaces-étale
total ringed site of a simplicial algebraic space. -/
instance hasWeakSheafify_etaleTotalRingedSite_over :
    ∀ x, HasWeakSheafify ((etaleTotalRingedSite U).siteTopology.over x)
      AddCommGrpCat.{u} :=
  sorry

/-- Sheafification equivalences on slices of the spaces-étale total ringed site of a
simplicial algebraic space are exactly the locally bijective morphisms. -/
instance wEqualsLocallyBijective_etaleTotalRingedSite_over :
    ∀ x, ((etaleTotalRingedSite U).siteTopology.over x).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  sorry

/-- The object property of quasi-coherent module sheaves on `U_spaces,étale`. -/
abbrev quasiCoherentModuleProperty :
    ObjectProperty (RingedSite.ModuleCat.{u} (etaleTotalRingedSite U)) :=
  SheafOfModules.isQuasicoherent (etaleTotalRingedSite U).structureSheaf

/-- `quasiCoherentModuleProperty U` is mathlib's quasi-coherence predicate on the
structure sheaf of the spaces-étale total ringed site. -/
theorem quasiCoherentModuleProperty_eq :
    quasiCoherentModuleProperty U =
      SheafOfModules.isQuasicoherent (etaleTotalRingedSite U).structureSheaf :=
  sorry

/-- A module sheaf on `U_spaces,étale` lies in `quasiCoherentModuleProperty U` if and
only if it is quasi-coherent. -/
theorem mem_QCoh_iff {M : RingedSite.ModuleCat.{u} (etaleTotalRingedSite U)} :
    quasiCoherentModuleProperty U M ↔ M.IsQuasicoherent :=
  sorry

/-- The category `QCoh(𝒪_U)` of quasi-coherent modules on the spaces-étale total
ringed site of a simplicial algebraic space. -/
abbrev QCoh :=
  (quasiCoherentModuleProperty U).FullSubcategory

namespace QCoh

/-- The inclusion of quasi-coherent modules into all module sheaves on
`U_spaces,étale`. -/
abbrev inclusion : QCoh U ⥤ RingedSite.ModuleCat.{u} (etaleTotalRingedSite U) :=
  (quasiCoherentModuleProperty U).ι

/-- Package a quasi-coherent module sheaf on `U_spaces,étale` as an object of
`QCoh U`. -/
abbrev of (M : RingedSite.ModuleCat.{u} (etaleTotalRingedSite U))
    (hM : quasiCoherentModuleProperty U M) : QCoh U :=
  ⟨M, hM⟩

end QCoh

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
