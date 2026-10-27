/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalScheme.Ideal
public import Mathlib.Order.Directed
public import Mathlib.Topology.QuasiSeparated

/-!
# Fundamental systems of ideals of definition

A fundamental system of ideals of definition on an EGA formal scheme is a
family of ideals of definition which, on every formal affine open, is a
neighbourhood basis of `0`.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Opposite TopologicalSpace Topology AlgebraicGeometry
open TopologicalRing

namespace AlgebraicGeometry.FormalScheme

open TopologicalRing.Ideal

/-- A fundamental system of ideals of definition on an EGA formal scheme. -/
structure FundamentalSystem (X : FormalScheme.{u}) where
  /-- Index type of the family. -/
  ι : Type u
  /-- The family of ideal sheaves. -/
  ideal : ι → IdealSheafData X
  /-- Each member is an ideal of definition. -/
  isIdeal : ∀ i, IsIdealOfDefinition (ideal i)
  /-- On every formal affine open, the section ideals form a neighbourhood
  basis of `0`. -/
  hasBasis :
    ∀ U : X.affineOpens,
      (nhds (0 : (X.presheaf.obj (op U.1) : Type u))).HasBasis
        (fun _ : ι ↦ True) (fun i ↦ ((ideal i).ideal U : Set _))

/-- Extensions of all defining ideals form a basis at zero on every affine open. -/
theorem FundamentalSystem.ofSpf_hasBasis (A : TopCommRingCat.{u})
    (hA : IsAdmissibleRing A) (U : (FormalScheme.ofSpf A hA).affineOpens) :
    (nhds (0 : ((FormalScheme.ofSpf A hA).presheaf.obj (op U.1) : Type u))).HasBasis
      (fun _ : TopologicalRing.IdealOfDefinition A ↦ True)
      (fun J ↦ ((IdealSheafData.ofSpf A hA J.val J.property.1).ideal U : Set _)) :=
  sorry

/-- The tautological system on an admissible formal spectrum is indexed by its defining ideals. -/
def FundamentalSystem.ofSpf (A : TopCommRingCat.{u}) (hA : IsAdmissibleRing A) :
    FundamentalSystem (FormalScheme.ofSpf A hA) where
  ι := TopologicalRing.IdealOfDefinition A
  ideal := fun J ↦ IdealSheafData.ofSpf A hA J.val J.property.1
  isIdeal := isIdealOfDefinition_ofSpf A hA
  hasBasis := FundamentalSystem.ofSpf_hasBasis A hA

/-- The index type of `FundamentalSystem.ofSpf A hA` is the type of ideals of
definition of `A`. -/
theorem FundamentalSystem.ofSpf_ι (A : TopCommRingCat.{u})
    (hA : IsAdmissibleRing A) :
    (FundamentalSystem.ofSpf A hA).ι =
      TopologicalRing.IdealOfDefinition A :=
  rfl

/-- Members of `FundamentalSystem.ofSpf A hA` are the `ofSpf` ideal sheaves. -/
theorem FundamentalSystem.ofSpf_ideal (A : TopCommRingCat.{u})
    (hA : IsAdmissibleRing A)
    (J : TopologicalRing.IdealOfDefinition A) :
    (FundamentalSystem.ofSpf A hA).ideal J =
      IdealSheafData.ofSpf A hA J.val J.property.1 :=
  rfl

/-- A family of ideal sheaves is a fundamental system of ideals of definition
when on every formal affine open the section ideals form a ring-level
fundamental system of ideals of definition. -/
def IsFundamentalSystem {X : FormalScheme.{u}} {ι : Type u}
    (I : ι → IdealSheafData X) : Prop :=
  ∀ U : X.affineOpens,
      IsFundamentalSystemOfIdeals (fun i ↦ (I i).ideal U)

/-- Unfolding of `IsFundamentalSystem`. -/
theorem isFundamentalSystem_iff {X : FormalScheme.{u}} {ι : Type u}
    (I : ι → IdealSheafData X) :
    IsFundamentalSystem I ↔
      ∀ U : X.affineOpens,
        IsFundamentalSystemOfIdeals (fun i ↦ (I i).ideal U) :=
  Iff.rfl

/-- A bundled fundamental system is a fundamental system on its family. -/
theorem FundamentalSystem.isFundamental {X : FormalScheme.{u}} (S : FundamentalSystem X) :
    IsFundamentalSystem S.ideal :=
  fun U ↦ ⟨fun i ↦ S.isIdeal i U, S.hasBasis U⟩

/-- Package a family of ideal sheaves that is a fundamental system. -/
def FundamentalSystem.ofFamily {X : FormalScheme.{u}} {ι : Type u}
    (I : ι → IdealSheafData X) (hI : IsFundamentalSystem I) :
    FundamentalSystem X where
  ι := ι
  ideal := I
  isIdeal i U := (hI U).1 i
  hasBasis U := (hI U).2

/-- The index type of `FundamentalSystem.ofFamily I hI` is the given index. -/
theorem FundamentalSystem.ofFamily_ι {X : FormalScheme.{u}} {ι : Type u}
    (I : ι → IdealSheafData X) (hI : IsFundamentalSystem I) :
    (FundamentalSystem.ofFamily I hI).ι = ι :=
  rfl

/-- Members of `FundamentalSystem.ofFamily I hI` are the given family. -/
theorem FundamentalSystem.ofFamily_ideal {X : FormalScheme.{u}} {ι : Type u}
    (I : ι → IdealSheafData X) (hI : IsFundamentalSystem I) :
    (FundamentalSystem.ofFamily I hI).ideal = I :=
  rfl

/-- A nonempty simultaneously downward-directed family is fundamental exactly when it is
fundamental on an affine open covering. -/
theorem isFundamentalSystem_iff_affineCover {X : FormalScheme.{u}} {ι : Type u}
    (I : ι → IdealSheafData X)
    (hne : Nonempty ι)
    (hdir : ∀ i j : ι, ∃ k : ι, ∀ U : X.affineOpens,
      (I k).ideal U ≤ (I i).ideal U ∧ (I k).ideal U ≤ (I j).ideal U)
    {κ : Type u} (𝒰 : κ → X.affineOpens)
    (hcover : ⨆ j, (𝒰 j).1 = ⊤) :
    IsFundamentalSystem I ↔
      ∀ j, IsFundamentalSystemOfIdeals (fun i ↦ (I i).ideal (𝒰 j)) :=
  sorry

/-- Every quasi-compact and quasi-separated EGA formal scheme has a fundamental
system of ideals of definition. -/
theorem exists_fundamentalSystem (X : FormalScheme.{u})
    [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier] :
    Nonempty (FundamentalSystem X) := sorry

end AlgebraicGeometry.FormalScheme
