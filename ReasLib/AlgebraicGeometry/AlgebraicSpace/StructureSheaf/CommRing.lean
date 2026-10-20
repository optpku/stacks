/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.ULift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Basic
public import ReasLib.Algebra.Category.Ring.Sheaf

/-!
# Commutative structure sheaf on the small étale site of an algebraic space

The structure sheaf `𝒪_X` is the global-sections functor `U ↦ Γ(U, 𝒪_U)`, retained as a
sheaf of commutative rings so that tensor products and internal Hom of `𝒪_X`-modules are the
canonical ringed-site operations.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The commutative-ring-valued global-sections presheaf on the small étale site of `X`. -/
abbrev commStructurePresheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (smallEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u} :=
  (smallEtaleToScheme X).op ⋙ Scheme.Γ

/-- The value of `commStructurePresheaf X` at `U` is the global-sections ring of the underlying
scheme. -/
theorem commStructurePresheaf_obj {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallEtaleSite X) :
    (commStructurePresheaf X).obj (op U) = CommRingCat.of Γ(U.left.left, ⊤) :=
  sorry

/-- Forgetting commutativity of `commStructurePresheaf X` recovers `structurePresheaf X`. -/
theorem structurePresheaf_eq_forget_comm {S : Scheme.{u}} (X : AlgebraicSpace S) :
    structurePresheaf X = commStructurePresheaf X ⋙ forget₂ CommRingCat RingCat :=
  rfl

/-- The commutative global-sections presheaf on the small étale site of an algebraic space is a
sheaf. -/
theorem commStructurePresheaf_isSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Presheaf.IsSheaf (smallEtaleTopology X) (commStructurePresheaf X) :=
  sorry

/-- The structure sheaf `𝒪_X` as a sheaf of commutative rings on the small étale site. -/
def commStructureSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} :=
  ⟨commStructurePresheaf X, commStructurePresheaf_isSheaf X⟩

/-- The underlying presheaf of `commStructureSheaf X` is `commStructurePresheaf X`. -/
theorem commStructureSheaf_val {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (commStructureSheaf X).obj = commStructurePresheaf X :=
  rfl

/-- Commutative-ring-valued sheaf composition exists on the small étale topology of an algebraic
space. -/
instance smallEtaleTopology_hasSheafCompose_commRing {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    (smallEtaleTopology X).HasSheafCompose
      (forget₂ CommRingCat.{u} RingCat.{u}) :=
  sorry

/-- The universe lift of `commStructurePresheaf X`, landing in `CommRingCat.{u + 1}` so that
internal Hom is available on the large small étale site. -/
abbrev commStructurePresheafLift {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (smallEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  commStructurePresheaf X ⋙ CommRingCat.universeLift.{u, u + 1}

/-- The lifted commutative global-sections presheaf is a sheaf. -/
theorem commStructurePresheafLift_isSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Presheaf.IsSheaf (smallEtaleTopology X) (commStructurePresheafLift X) :=
  sorry

/-- The universe-lifted commutative structure sheaf on the small étale site of `X`. -/
def commStructureSheafLift {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u + 1} :=
  ⟨commStructurePresheafLift X, commStructurePresheafLift_isSheaf X⟩

/-- The underlying presheaf of `commStructureSheafLift X` is `commStructurePresheafLift X`. -/
theorem commStructureSheafLift_val {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (commStructureSheafLift X).obj = commStructurePresheafLift X :=
  rfl

/-- Abelian-group-valued sheaf composition exists for `AddCommGrpCat.{u + 1}` on the small étale
topology of an algebraic space. -/
instance smallEtaleTopology_hasSheafCompose_addCommGrp_succ {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    (smallEtaleTopology X).HasSheafCompose
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) :=
  sorry

/-- Abelian-group-valued weak sheafification exists in universe `u + 1` on the small étale
topology of an algebraic space. -/
instance smallEtaleTopology_hasWeakSheafify_addCommGrp_succ {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    HasWeakSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1} :=
  sorry

/-- On the small étale topology of an algebraic space, sheafification equivalences in universe
`u + 1` are the locally bijective morphisms. -/
instance smallEtaleTopology_wEqualsLocallyBijective_succ {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    (smallEtaleTopology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
