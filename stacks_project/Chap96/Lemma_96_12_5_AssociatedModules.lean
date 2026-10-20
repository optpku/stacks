/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Ring.ULift
public import ReasLib.Algebra.Category.CommRingCat.ULift
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import stacks_project.Chap96.Definition_96_11_1_QCoh
public import stacks_project.Chap96.Lemma_96_8_1_RingedSite

/-!
# Associated module categories of a category fibred in groupoids

A category fibred in groupoids `X` over `(Sch/S)_fppf` carries an associated
`τ`-ringed site `(X_τ, 𝒪_X)` for each standard topology `τ`. This file names
the module category `Mod(X_τ, 𝒪_X)`, its commutative presentation (needed for
tensor and internal Hom), and the universe lift used by internal Hom.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Ring-to-abelian-group sheaf composition exists on an associated `τ`-topology. -/
instance associatedTopology_hasSheafCompose_ring_addCommGrp
    (X : GroupoidsOver S) (τ : StandardTopology) :
    (X.associatedTopology τ).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  sorry

/-- Commutative-ring-to-ring sheaf composition exists on an associated `τ`-topology. -/
instance associatedTopology_hasSheafCompose_commRing
    (X : GroupoidsOver S) (τ : StandardTopology) :
    (X.associatedTopology τ).HasSheafCompose
      (forget₂ CommRingCat.{u} RingCat.{u}) :=
  sorry

/-- Commutative-ring-to-ring sheaf composition exists in universe `u + 1` on an
associated `τ`-topology. -/
instance associatedTopology_hasSheafCompose_commRing_succ
    (X : GroupoidsOver S) (τ : StandardTopology) :
    (X.associatedTopology τ).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  sorry

/-- Abelian-group-valued weak sheafification exists on an associated `τ`-topology. -/
instance associatedTopology_hasWeakSheafify
    (X : GroupoidsOver S) (τ : StandardTopology) :
    HasWeakSheafify (X.associatedTopology τ) AddCommGrpCat.{u} :=
  sorry

/-- On an associated `τ`-topology, sheafification equivalences are the locally
bijective morphisms. -/
instance associatedTopology_wEqualsLocallyBijective
    (X : GroupoidsOver S) (τ : StandardTopology) :
    (X.associatedTopology τ).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  sorry

/-- Abelian-group-valued sheaf composition exists in universe `u + 1` on an
associated `τ`-topology. -/
instance associatedTopology_hasSheafCompose_addCommGrp_succ
    (X : GroupoidsOver S) (τ : StandardTopology) :
    (X.associatedTopology τ).HasSheafCompose
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) :=
  sorry

/-- Abelian-group-valued weak sheafification exists in universe `u + 1` on an
associated `τ`-topology. -/
instance associatedTopology_hasWeakSheafify_succ
    (X : GroupoidsOver S) (τ : StandardTopology) :
    HasWeakSheafify (X.associatedTopology τ) AddCommGrpCat.{u + 1} :=
  sorry

/-- On an associated `τ`-topology, sheafification equivalences in universe `u + 1`
are the locally bijective morphisms. -/
instance associatedTopology_wEqualsLocallyBijective_succ
    (X : GroupoidsOver S) (τ : StandardTopology) :
    (X.associatedTopology τ).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  sorry

/-- Weak sheafification of abelian groups exists on every slice of an associated
`τ`-ringed site. -/
instance associatedRingedSite_over_hasWeakSheafify (X : GroupoidsOver S)
    (τ : StandardTopology) :
    ∀ U, HasWeakSheafify ((associatedRingedSite X τ).siteTopology.over U)
      AddCommGrpCat.{u} :=
  sorry

/-- Sheafification equivalences on slices of an associated `τ`-ringed site are
the locally bijective morphisms. -/
instance associatedRingedSite_over_wEqualsLocallyBijective
    (X : GroupoidsOver S) (τ : StandardTopology) :
    ∀ U, ((associatedRingedSite X τ).siteTopology.over U).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  sorry

/-- Weak sheafification exists on slices of an associated `τ`-topology. -/
instance associatedTopology_over_hasWeakSheafify (X : GroupoidsOver S)
    (τ : StandardTopology) :
    ∀ U, HasWeakSheafify ((X.associatedTopology τ).over U) AddCommGrpCat.{u} :=
  sorry

/-- Sheafification equivalences on slices of an associated `τ`-topology are the
locally bijective morphisms. -/
instance associatedTopology_over_wEqualsLocallyBijective
    (X : GroupoidsOver S) (τ : StandardTopology) :
    ∀ U, ((X.associatedTopology τ).over U).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  sorry

/-- Weak sheafification exists on double slices of an associated `τ`-topology. -/
instance associatedTopology_over_over_hasWeakSheafify (X : GroupoidsOver S)
    (τ : StandardTopology) :
    ∀ U, ∀ V : Over U,
      HasWeakSheafify (((X.associatedTopology τ).over U).over V)
        AddCommGrpCat.{u} :=
  sorry

/-- Sheafification equivalences on double slices of an associated `τ`-topology
are the locally bijective morphisms. -/
instance associatedTopology_over_over_wEqualsLocallyBijective
    (X : GroupoidsOver S) (τ : StandardTopology) :
    ∀ U, ∀ V : Over U,
      (((X.associatedTopology τ).over U).over V).WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
  sorry

/-- The category of sheaves of modules on `(X_τ, 𝒪_X)`. -/
abbrev associatedModules (X : GroupoidsOver S) (τ : StandardTopology) :=
  RingedSite.ModuleCat.{u} (associatedRingedSite X τ)

/-- `associatedModules X τ` is the module category of the associated `τ`-ringed
site of `X`. -/
theorem associatedModules_eq (X : GroupoidsOver S) (τ : StandardTopology) :
    associatedModules X τ =
      RingedSite.ModuleCat.{u} (associatedRingedSite X τ) :=
  sorry

/-- The associated module category has colimits of every universe-compatible
shape. -/
instance associatedModules_hasColimitsOfShape (X : GroupoidsOver S)
    (τ : StandardTopology) (J : Type u) [Category.{u} J] :
    HasColimitsOfShape J (associatedModules X τ) :=
  sorry

/-- The fppf module category of `X` has colimits of every universe-compatible
shape. -/
instance fppfModules_hasColimitsOfShape (X : GroupoidsOver S)
    (J : Type u) [Category.{u} J] :
    HasColimitsOfShape J (RingedSite.ModuleCat.{u} (fppfRingedSite X)) :=
  sorry

/-- The commutative global-sections presheaf on the big `τ`-site of `S` is a
sheaf. -/
theorem bigCommStructurePresheaf_isSheaf (τ : StandardTopology) :
    Presheaf.IsSheaf (τ.overTopology S) ((Over.forget S).op ⋙ Scheme.Γ) :=
  sorry

/-- The commutative structure sheaf on the big `τ`-site of `S`. -/
def bigCommStructureSheaf (τ : StandardTopology) :
    Sheaf (τ.overTopology S) CommRingCat.{u} :=
  ⟨(Over.forget S).op ⋙ Scheme.Γ, bigCommStructurePresheaf_isSheaf τ⟩

/-- The commutative structure sheaf `𝒪_X` on the associated `τ`-site, obtained as
the inverse image `p⁻¹ 𝒪` of the big `τ`-commutative structure sheaf. -/
def commAssociatedStructureSheaf (X : GroupoidsOver S) (τ : StandardTopology) :
    Sheaf (X.associatedTopology τ) CommRingCat.{u} :=
  (X.p.sheafPushforwardContinuous CommRingCat.{u}
      (X.associatedTopology τ) (τ.overTopology S)).obj
    (bigCommStructureSheaf τ)

/-- `commAssociatedStructureSheaf` is the continuous pushforward of the big `τ`
commutative structure sheaf along the projection of `X`. -/
theorem commAssociatedStructureSheaf_def (X : GroupoidsOver S)
    (τ : StandardTopology) :
    commAssociatedStructureSheaf X τ =
      (X.p.sheafPushforwardContinuous CommRingCat.{u}
          (X.associatedTopology τ) (τ.overTopology S)).obj
        (bigCommStructureSheaf τ) :=
  sorry

/-- The associated `τ`-site of `X`, with commutative structure sheaf `𝒪_X`. -/
abbrev commAssociatedRingedSite (X : GroupoidsOver S) (τ : StandardTopology) :
    RingedSite.{u + 1, u, u} :=
  RingedSite.ofCommRingSheaf (X.associatedTopology τ)
    (commAssociatedStructureSheaf X τ)

/-- The structure sheaf of `commAssociatedRingedSite X τ` is the ring sheaf
underlying the commutative associated structure sheaf. -/
theorem commAssociatedRingedSite_structureSheaf (X : GroupoidsOver S)
    (τ : StandardTopology) :
    (commAssociatedRingedSite X τ).structureSheaf =
      CategoryTheory.Sheaf.ringSheafOfComm (commAssociatedStructureSheaf X τ) :=
  sorry

/-- The category of sheaves of modules on the commutative associated `τ`-ringed
site of `X`. -/
abbrev commAssociatedModules (X : GroupoidsOver S) (τ : StandardTopology) :=
  RingedSite.ModuleCat.{u} (commAssociatedRingedSite X τ)

/-- `commAssociatedModules` is the module category of
`commAssociatedRingedSite`. -/
theorem commAssociatedModules_eq (X : GroupoidsOver S) (τ : StandardTopology) :
    commAssociatedModules X τ =
      RingedSite.ModuleCat.{u} (commAssociatedRingedSite X τ) :=
  sorry

/-- The commutative associated module category has colimits of every
universe-compatible shape. -/
instance commAssociatedModules_hasColimitsOfShape (X : GroupoidsOver S)
    (τ : StandardTopology) (J : Type u) [Category.{u} J] :
    HasColimitsOfShape J (commAssociatedModules X τ) :=
  sorry

/-- Tensor product of modules on the commutative associated `τ`-site. -/
noncomputable abbrev moduleTensorAssociated {X : GroupoidsOver S}
    {τ : StandardTopology} (F G : commAssociatedModules X τ) :
    commAssociatedModules X τ :=
  SheafOfModules.RingedSite.moduleTensor.{u + 1, u, u} F G

/-- `moduleTensorAssociated` is the ringed-site tensor product. -/
theorem moduleTensorAssociated_eq {X : GroupoidsOver S} {τ : StandardTopology}
    (F G : commAssociatedModules X τ) :
    moduleTensorAssociated F G =
      SheafOfModules.RingedSite.moduleTensor.{u + 1, u, u} F G :=
  sorry

/-- The universe lift of the commutative associated `τ`-structure presheaf. -/
abbrev commAssociatedStructurePresheafLift (X : GroupoidsOver S)
    (τ : StandardTopology) :
    X.totalᵒᵖ ⥤ CommRingCat.{u + 1} :=
  (commAssociatedStructureSheaf X τ).obj ⋙ CommRingCat.universeLift.{u, u + 1}

/-- The lifted commutative associated structure presheaf is a sheaf. -/
theorem commAssociatedStructurePresheafLift_isSheaf (X : GroupoidsOver S)
    (τ : StandardTopology) :
    Presheaf.IsSheaf (X.associatedTopology τ)
      (commAssociatedStructurePresheafLift X τ) :=
  sorry

/-- The universe-lifted commutative structure sheaf on the associated `τ`-site. -/
def commAssociatedStructureSheafLift (X : GroupoidsOver S)
    (τ : StandardTopology) :
    Sheaf (X.associatedTopology τ) CommRingCat.{u + 1} :=
  ⟨commAssociatedStructurePresheafLift X τ,
    commAssociatedStructurePresheafLift_isSheaf X τ⟩

/-- The associated `τ`-site equipped with the universe-lifted commutative
structure sheaf. -/
abbrev commAssociatedRingedSiteLift (X : GroupoidsOver S)
    (τ : StandardTopology) : RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofCommSheafMax (X.associatedTopology τ)
    (commAssociatedStructureSheafLift X τ)

/-- The structure sheaf of `commAssociatedRingedSiteLift X τ` is the underlying
ring sheaf of the lifted commutative structure sheaf. -/
theorem commAssociatedRingedSiteLift_structureSheaf (X : GroupoidsOver S)
    (τ : StandardTopology) :
    (commAssociatedRingedSiteLift X τ).structureSheaf =
      CategoryTheory.Sheaf.ringSheafOfComm
        (commAssociatedStructureSheafLift X τ) :=
  sorry

/-- The category of universe-lifted modules on the commutative associated
`τ`-site of `X`. -/
abbrev commAssociatedModulesLift (X : GroupoidsOver S) (τ : StandardTopology) :=
  RingedSite.ModuleCat.{u + 1} (commAssociatedRingedSiteLift X τ)

/-- Tensor product of universe-lifted modules on the commutative associated
`τ`-site. -/
noncomputable abbrev moduleTensorAssociatedLift {X : GroupoidsOver S}
    {τ : StandardTopology} (F G : commAssociatedModulesLift X τ) :
    commAssociatedModulesLift X τ :=
  SheafOfModules.RingedSite.moduleTensor.{u + 1, u, u + 1} F G

end AlgebraicGeometry.GroupoidsOver
