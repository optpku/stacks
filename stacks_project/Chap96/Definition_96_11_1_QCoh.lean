module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import stacks_project.Chap96.Definition_96_4_1_AssociatedTopology
public import stacks_project.Chap96.Definition_96_6_1_StructureSheaf

/-!
# Quasi-coherent modules on a category fibred in groupoids

A quasi-coherent `𝒪_𝒳`-module is a module sheaf on the fppf ringed site of a
category fibred in groupoids that is quasi-coherent in the sense of
`SheafOfModules.IsQuasicoherent`. The category of such sheaves is the
corresponding full subcategory `QCoh`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} (X : GroupoidsOver S)

/-- The fppf ringed site `(𝒳_fppf, 𝒪_𝒳)` of a category fibred in groupoids. -/
abbrev fppfRingedSite : RingedSite.{u + 1, u, u} :=
  X.ringedSite

/-- The site of `fppfRingedSite X` is the associated fppf topology of `X`. -/
theorem fppfRingedSite_siteTopology :
    (fppfRingedSite X).siteTopology = X.fppfTopology :=
  sorry

/-- The structure sheaf of `fppfRingedSite X` is `𝒪_X`. -/
theorem fppfRingedSite_structureSheaf :
    (fppfRingedSite X).structureSheaf = X.structureSheaf :=
  sorry

/-- Abelian-group-valued sheaf composition exists on every slice of the fppf
ringed site of a category fibred in groupoids. -/
instance hasSheafCompose_fppfRingedSite_over :
    ∀ x, ((fppfRingedSite X).siteTopology.over x).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  sorry

/-- Weak sheafification of abelian groups exists on every slice of the fppf
ringed site of a category fibred in groupoids. -/
instance hasWeakSheafify_fppfRingedSite_over :
    ∀ x, HasWeakSheafify ((fppfRingedSite X).siteTopology.over x)
      AddCommGrpCat.{u} :=
  sorry

/-- Sheafification equivalences on slices of the fppf ringed site of a category
fibred in groupoids are exactly the locally bijective morphisms. -/
instance wEqualsLocallyBijective_fppfRingedSite_over :
    ∀ x, ((fppfRingedSite X).siteTopology.over x).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  sorry

/-- The object property of quasi-coherent module sheaves on `𝒳`. -/
abbrev quasiCoherentModuleProperty :
    ObjectProperty (RingedSite.ModuleCat.{u} (fppfRingedSite X)) :=
  SheafOfModules.isQuasicoherent (fppfRingedSite X).structureSheaf

/-- `quasiCoherentModuleProperty X` is mathlib's quasi-coherence predicate on
the structure sheaf of the fppf ringed site. -/
theorem quasiCoherentModuleProperty_eq :
    quasiCoherentModuleProperty X =
      SheafOfModules.isQuasicoherent (fppfRingedSite X).structureSheaf :=
  sorry

/-- A module sheaf on `𝒳` lies in `quasiCoherentModuleProperty X` if and only
if it is quasi-coherent. -/
theorem mem_QCoh_iff {M : RingedSite.ModuleCat.{u} (fppfRingedSite X)} :
    quasiCoherentModuleProperty X M ↔ M.IsQuasicoherent :=
  sorry

/-- The category `QCoh(𝒪_𝒳)` of quasi-coherent modules on a category fibred in
groupoids. -/
abbrev QCoh :=
  (quasiCoherentModuleProperty X).FullSubcategory

namespace QCoh

/-- The inclusion of quasi-coherent modules into all module sheaves on the fppf
ringed site of `X`. -/
abbrev inclusion : QCoh X ⥤ RingedSite.ModuleCat.{u} (fppfRingedSite X) :=
  (quasiCoherentModuleProperty X).ι

end QCoh

end AlgebraicGeometry.GroupoidsOver
