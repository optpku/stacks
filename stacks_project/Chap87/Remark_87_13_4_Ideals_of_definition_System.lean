/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.Remark_87_13_4_Ideals_of_definition_Ideal

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

namespace TopologicalRing.Ideal

/-- A family of ideals of a topological ring is a fundamental system of ideals
of definition when each member is an ideal of definition and the family is a
neighbourhood basis of `0`. -/
class IsFundamentalSystemOfIdeals {A : Type u} [CommRing A] [TopologicalSpace A]
    {ι : Type u} (I : ι → Ideal A) : Prop where
  /-- Each member is an ideal of definition. -/
  isIdeal : ∀ i, IsIdealOfDefinition (I i)
  /-- The family is a neighbourhood basis of `0`. -/
  hasBasis : (nhds (0 : A)).HasBasis (fun _ : ι ↦ True) (fun i ↦ (I i : Set A))

/-- Unfolding of `IsFundamentalSystemOfIdeals`. -/
theorem isFundamentalSystemOfIdeals_iff {A : Type u} [CommRing A]
    [TopologicalSpace A] {ι : Type u} (I : ι → Ideal A) :
    IsFundamentalSystemOfIdeals I ↔
      (∀ i, IsIdealOfDefinition (I i)) ∧
        (nhds (0 : A)).HasBasis (fun _ : ι ↦ True) (fun i ↦ (I i : Set A)) :=
  sorry

/-- All ideals of definition of a pre-admissible ring form a fundamental
system. -/
instance instIsFundamentalSystemOfIdeals_idealOfDefinition {A : Type u}
    [CommRing A] [TopologicalSpace A] [IsPreadmissibleRing A] :
    IsFundamentalSystemOfIdeals
      (fun J : AffineFormalAlgebraicSpace.IdealOfDefinition A ↦ J.ideal) :=
  sorry

end TopologicalRing.Ideal

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

/-- The tautological fundamental system of `ofSpf A`, indexed by all ideals of
definition of `A`. -/
def FundamentalSystem.ofSpf (A : TopCommRingCat.{u}) (hA : IsAdmissibleRing A) :
    FundamentalSystem (FormalScheme.ofSpf A hA) where
  ι := AffineFormalAlgebraicSpace.IdealOfDefinition A
  ideal := fun J ↦ IdealSheafData.ofSpf A hA J.ideal
  isIdeal := fun _ ↦ sorry
  hasBasis := sorry

/-- The index type of `FundamentalSystem.ofSpf A hA` is the type of ideals of
definition of `A`. -/
theorem FundamentalSystem.ofSpf_ι (A : TopCommRingCat.{u})
    (hA : IsAdmissibleRing A) :
    (FundamentalSystem.ofSpf A hA).ι =
      AffineFormalAlgebraicSpace.IdealOfDefinition A :=
  sorry

/-- Members of `FundamentalSystem.ofSpf A hA` are the `ofSpf` ideal sheaves. -/
theorem FundamentalSystem.ofSpf_ideal (A : TopCommRingCat.{u})
    (hA : IsAdmissibleRing A)
    (J : AffineFormalAlgebraicSpace.IdealOfDefinition A) :
    (FundamentalSystem.ofSpf A hA).ideal J =
      IdealSheafData.ofSpf A hA J.ideal :=
  sorry

/-- A family of ideal sheaves is a fundamental system of ideals of definition
when on every formal affine open the section ideals form a ring-level
fundamental system of ideals of definition. -/
class IsFundamentalSystem {X : FormalScheme.{u}} {ι : Type u}
    (I : ι → IdealSheafData X) : Prop where
  /-- Affine-open section ideals form a ring-level fundamental system. -/
  isFundamental :
    ∀ U : X.affineOpens,
      IsFundamentalSystemOfIdeals (fun i ↦ (I i).ideal U)

/-- Unfolding of `IsFundamentalSystem`. -/
theorem isFundamentalSystem_iff {X : FormalScheme.{u}} {ι : Type u}
    (I : ι → IdealSheafData X) :
    IsFundamentalSystem I ↔
      ∀ U : X.affineOpens,
        IsFundamentalSystemOfIdeals (fun i ↦ (I i).ideal U) :=
  sorry

/-- A bundled fundamental system is a fundamental system on its family. -/
instance instIsFundamentalSystem {X : FormalScheme.{u}} (S : FundamentalSystem X) :
    IsFundamentalSystem S.ideal :=
  sorry

/-- Package a family of ideal sheaves that is a fundamental system. -/
def FundamentalSystem.ofFamily {X : FormalScheme.{u}} {ι : Type u}
    (I : ι → IdealSheafData X) (hI : IsFundamentalSystem I) :
    FundamentalSystem X where
  ι := ι
  ideal := I
  isIdeal := sorry
  hasBasis := sorry

/-- The index type of `FundamentalSystem.ofFamily I hI` is the given index. -/
theorem FundamentalSystem.ofFamily_ι {X : FormalScheme.{u}} {ι : Type u}
    (I : ι → IdealSheafData X) (hI : IsFundamentalSystem I) :
    (FundamentalSystem.ofFamily I hI).ι = ι :=
  sorry

/-- Members of `FundamentalSystem.ofFamily I hI` are the given family. -/
theorem FundamentalSystem.ofFamily_ideal {X : FormalScheme.{u}} {ι : Type u}
    (I : ι → IdealSheafData X) (hI : IsFundamentalSystem I) :
    (FundamentalSystem.ofFamily I hI).ideal = I :=
  sorry

/-- Being a fundamental system of ideals of definition may be checked on the
members of an affine open covering. -/
theorem isFundamentalSystem_iff_affineCover {X : FormalScheme.{u}} {ι : Type u}
    (I : ι → IdealSheafData X) {κ : Type u} (𝒰 : κ → X.affineOpens)
    (hcover : ⨆ j, (𝒰 j).1 = ⊤) :
    IsFundamentalSystem I ↔
      ∀ j, IsFundamentalSystemOfIdeals (fun i ↦ (I i).ideal (𝒰 j)) :=
  sorry

end AlgebraicGeometry.FormalScheme
