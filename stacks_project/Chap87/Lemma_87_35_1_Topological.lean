/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Order
public import Mathlib.Topology.Category.TopCommRingCat
public import stacks_project.Chap87.Lemma_87_35_3_StructureSheaf

/-!
# Inverse-limit topology on stage global-section rings

The inverse-limit ring of stage global sections of a directed affine
thickening presentation carries the inverse-limit topology, making it a
topological commutative ring. Forgetting the topology on a sheaf of
topological rings yields a sheaf of rings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.AffineFormalAlgebraicSpace (AffineEtaleOver)
open scoped Topology

noncomputable section

universe u v w

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Forget the topology on the values of a sheaf of topological commutative
rings, landing in `RingCat`. -/
def topCommRingSheafToRingSheaf {C : Type v} [Category.{w} C]
    {J : GrothendieckTopology C} (𝒪 : Sheaf J TopCommRingCat.{u}) :
    Sheaf J RingCat.{u} :=
  ⟨𝒪.obj ⋙ forget₂ TopCommRingCat CommRingCat ⋙ forget₂ CommRingCat RingCat,
    sorry⟩

/-- The underlying ring of a forgotten topological-ring sheaf at `U` is the
forgetful image of the topological-ring value. -/
theorem topCommRingSheafToRingSheaf_obj {C : Type v} [Category.{w} C]
    {J : GrothendieckTopology C} (𝒪 : Sheaf J TopCommRingCat.{u}) (U : Cᵒᵖ) :
    (topCommRingSheafToRingSheaf 𝒪).obj.obj U =
      (forget₂ TopCommRingCat CommRingCat ⋙ forget₂ CommRingCat RingCat).obj
        (𝒪.obj.obj U) :=
  sorry

variable {S : Scheme.{u}}

/-- Carrier of the inverse-limit ring of stage global sections of a diagram of
schemes over `S`. -/
def StageLimitCarrier {Λ : Type u} [Preorder Λ] (D : Λ ⥤ Over S) : Type u :=
  (stageLimitRing D : Type u)

/-- `StageLimitCarrier D` is the underlying type of `stageLimitRing D`. -/
theorem StageLimitCarrier_eq {Λ : Type u} [Preorder Λ] (D : Λ ⥤ Over S) :
    StageLimitCarrier D = (stageLimitRing D : Type u) :=
  sorry

/-- The inverse-limit carrier inherits the ring structure of `stageLimitRing`. -/
instance instRingStageLimitCarrier {Λ : Type u} [Preorder Λ] (D : Λ ⥤ Over S) :
    Ring (StageLimitCarrier D) :=
  inferInstanceAs (Ring (stageLimitRing D : Type u))

/-- Projection from the inverse-limit carrier onto the stage `i` ring. -/
def stageLimitTopRing_π {Λ : Type u} [Preorder Λ] (D : Λ ⥤ Over S) (i : Λ) :
    StageLimitCarrier D →+* (stageGlobalSectionsFunctor D).obj (op i) :=
  (stageLimitRing_π D i).hom

/-- Inverse-limit topology on `StageLimitCarrier D`: the infimum of the
topologies induced by the stage projections from the discrete topology on each
stage ring. -/
@[reducible] def stageLimitTopology {Λ : Type u} [Preorder Λ] (D : Λ ⥤ Over S) :
    TopologicalSpace (StageLimitCarrier D) :=
  ⨅ i : Λ, TopologicalSpace.induced (stageLimitTopRing_π D i)
    (⊥ : TopologicalSpace ((stageGlobalSectionsFunctor D).obj (op i)))

/-- The topology on `StageLimitCarrier D` is the inverse-limit topology. -/
instance instTopologicalSpaceStageLimitCarrier {Λ : Type u} [Preorder Λ]
    (D : Λ ⥤ Over S) : TopologicalSpace (StageLimitCarrier D) :=
  stageLimitTopology D

/-- Stage global-section rings are commutative, so the inverse-limit carrier is
a commutative ring. -/
instance instCommRingStageLimitCarrier {Λ : Type u} [Preorder Λ]
    (D : Λ ⥤ Over S) : CommRing (StageLimitCarrier D) where
  toRing := inferInstanceAs (Ring (StageLimitCarrier D))
  mul_comm := sorry

/-- The inverse-limit topology makes the stage-limit carrier a topological
ring. -/
instance instIsTopologicalRingStageLimitCarrier {Λ : Type u} [Preorder Λ]
    (D : Λ ⥤ Over S) : IsTopologicalRing (StageLimitCarrier D) :=
  sorry

/-- The inverse-limit topology is the infimum of the topologies induced by the
discrete stage projections. -/
theorem stageLimitTopology_eq_iInf {Λ : Type u} [Preorder Λ] (D : Λ ⥤ Over S) :
    stageLimitTopology D =
      ⨅ i : Λ, TopologicalSpace.induced (stageLimitTopRing_π D i)
        (⊥ : TopologicalSpace ((stageGlobalSectionsFunctor D).obj (op i))) :=
  sorry

/-- Each stage projection is continuous for the inverse-limit topology when the
stage ring is discrete. -/
theorem stageLimitTopRing_π_continuous {Λ : Type u} [Preorder Λ]
    (D : Λ ⥤ Over S) (i : Λ) :
    Continuous[stageLimitTopology D, ⊥] (stageLimitTopRing_π D i) :=
  sorry

/-- The kernels of the stage projections are open additive subgroups of the
inverse-limit topology. -/
theorem isOpen_ker_stageLimitTopRing_π {Λ : Type u} [Preorder Λ]
    (D : Λ ⥤ Over S) (i : Λ) :
    IsOpen (RingHom.ker (stageLimitTopRing_π D i) : Set (StageLimitCarrier D)) :=
  sorry

/-- The kernels of the stage projections form a fundamental system of open
neighbourhoods of `0`. -/
theorem stageLimitTopology_hasBasis_ker {Λ : Type u} [Preorder Λ]
    [IsDirected Λ (· ≤ ·)] [Nonempty Λ] (D : Λ ⥤ Over S) :
    (nhds (0 : StageLimitCarrier D)).HasBasis (fun _ : Λ ↦ True)
      (fun i ↦ (RingHom.ker (stageLimitTopRing_π D i) : Set (StageLimitCarrier D))) :=
  sorry

/-- Inverse-limit ring of stage global sections, as a topological commutative
ring. -/
def stageLimitTopRing {Λ : Type u} [Preorder Λ] (D : Λ ⥤ Over S) :
    TopCommRingCat.{u} :=
  TopCommRingCat.of (StageLimitCarrier D)

/-- Forgetting the topology on `stageLimitTopRing D` recovers `stageLimitRing D`. -/
theorem stageLimitTopRing_iso_stageLimitRing {Λ : Type u} [Preorder Λ]
    (D : Λ ⥤ Over S) :
    (forget₂ TopCommRingCat CommRingCat ⋙ forget₂ CommRingCat RingCat).obj
      (stageLimitTopRing D) = stageLimitRing D :=
  sorry

/-- Forgetting only as far as commutative rings yields the commutative ring
underlying `stageLimitRing D`. -/
theorem stageLimitTopRing_forget {Λ : Type u} [Preorder Λ] (D : Λ ⥤ Over S) :
    ((forget₂ TopCommRingCat CommRingCat).obj (stageLimitTopRing D) : Type u) =
      (stageLimitRing D : Type u) :=
  sorry

/-- Value of a sheaf of topological rings on the affine étale object `U_red`. -/
abbrev structureSheafTopSections {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X]
    (𝒪 : Sheaf (smallEtaleTopology X) TopCommRingCat.{u})
    (U : AffineEtaleOver X) : TopCommRingCat.{u} :=
  𝒪.obj.obj
    (op ((AlgebraicSpace.affineEtaleInclusion (reduction X)).obj
        (toAffineEtale.obj U)))

/-- `structureSheafTopSections 𝒪 U` is the value of `𝒪` on the image of
`toAffineEtale.obj U` in the small étale site. -/
theorem structureSheafTopSections_obj {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X]
    (𝒪 : Sheaf (smallEtaleTopology X) TopCommRingCat.{u})
    (U : AffineEtaleOver X) :
    structureSheafTopSections 𝒪 U =
      𝒪.obj.obj
        (op ((AlgebraicSpace.affineEtaleInclusion (reduction X)).obj
            (toAffineEtale.obj U))) :=
  sorry

/-- Forgetting the topology on topological-ring sections recovers the ring-valued
structure-sheaf sections. -/
theorem forget_structureSheafTopSections {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X]
    (𝒪 : Sheaf (smallEtaleTopology X) TopCommRingCat.{u})
    (U : AffineEtaleOver X) :
    (forget₂ TopCommRingCat CommRingCat ⋙ forget₂ CommRingCat RingCat).obj
      (structureSheafTopSections 𝒪 U) =
      structureSheafSections (topCommRingSheafToRingSheaf 𝒪) U :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
