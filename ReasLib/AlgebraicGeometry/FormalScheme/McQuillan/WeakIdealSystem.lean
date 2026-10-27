/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.Order.Directed
public import ReasLib.RingTheory.Topology.WeakIdealSystem
public import ReasLib.AlgebraicGeometry.FormalScheme.McQuillan.WeakIdealQuotient
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.AlgebraicSpaceColimit

/-!
# Fundamental systems of weak ideals of definition

A fundamental system of weak ideals of definition on a McQuillan formal
scheme is a family of weak ideals of definition which, on every formal affine
open, is a neighbourhood basis of `0`. Existence of such a family is equivalent
to `h_X` being a directed colimit of schemes along thickenings.
-/

@[expose] public section

universe u v

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

namespace AlgebraicGeometry.McQuillan.FormalScheme

/-- A family of ideal sheaves is fundamental if its sections form a fundamental
system of weak ideals on every affine open. -/
def IsFundamentalSystem {X : FormalScheme.{u}} {ι : Type u}
    (I : ι → IdealSheafData X) : Prop :=
  ∀ U : X.affineOpens,
    TopologicalRing.IsFundamentalSystemOfWeakIdeals (fun i ↦ (I i).ideal U)

/-- A family is fundamental exactly when it is fundamental on every affine section ring. -/
theorem isFundamentalSystem_iff {X : FormalScheme.{u}} {ι : Type u}
    (I : ι → IdealSheafData X) :
    IsFundamentalSystem I ↔ ∀ U : X.affineOpens,
      TopologicalRing.IsFundamentalSystemOfWeakIdeals (fun i ↦ (I i).ideal U) :=
  Iff.rfl

/-- A fundamental system of weak ideals of definition on a McQuillan formal
scheme. -/
structure FundamentalSystem (X : FormalScheme.{u}) where
  /-- Index type of the family. -/
  ι : Type u
  /-- The family of ideal sheaves. -/
  ideal : ι → IdealSheafData X
  /-- Each member is a weak ideal of definition. -/
  isWeak : ∀ i, IsWeakIdealOfDefinition (ideal i)
  /-- On every formal affine open, the section ideals form a neighbourhood
  basis of `0`. -/
  hasBasis :
    ∀ U : X.affineOpens,
      (nhds (0 : (X.presheaf.obj (op U.1) : Type u))).HasBasis
        (fun _ : ι ↦ True) (fun i ↦ ((ideal i).ideal U : Set _))

/-- Package a family fundamental on every affine open as an explicit fundamental system. -/
def FundamentalSystem.ofFamily {X : FormalScheme.{u}} {ι : Type u}
    (I : ι → IdealSheafData X) (hI : IsFundamentalSystem I) : FundamentalSystem X where
  ι := ι
  ideal := I
  isWeak i U := (hI U).1 i
  hasBasis U := (hI U).2

/-- All weak quotient-projection kernels form a neighbourhood basis on every
formal affine open of a weak formal spectrum. -/
theorem ofSpfOnSpace_hasBasis (A : TopCommRingCat.{u}) (hA : IsWeaklyAdmissibleRing A)
    {T : Type u} [TopologicalSpace T]
    (e : T ≃ₜ AlgebraicGeometry.FormalSpectrum.OpenPrime (A : Type u))
    (U : (FormalScheme.ofSpfOnSpace A hA e).affineOpens) :
    (nhds (0 : ((FormalScheme.ofSpfOnSpace A hA e).presheaf.obj (op U.1) : Type u))).HasBasis
      (fun _ : {I : Ideal (A : Type u) //
        TopologicalRing.Ideal.IsWeakIdealOfDefinition I} ↦ True)
      (fun I ↦ ((IdealSheafData.ofSpfOnSpace A hA e I.val I.property).ideal U : Set _)) :=
  sorry

/-- The canonical fundamental system on a weak formal spectrum, indexed by all
weak ideals of its ring and using inverse-limit projection kernels as section ideals. -/
def FundamentalSystem.ofSpfOnSpace (A : TopCommRingCat.{u}) (hA : IsWeaklyAdmissibleRing A)
    {T : Type u} [TopologicalSpace T]
    (e : T ≃ₜ AlgebraicGeometry.FormalSpectrum.OpenPrime (A : Type u)) :
    FundamentalSystem (FormalScheme.ofSpfOnSpace A hA e) where
  ι := {I : Ideal (A : Type u) // TopologicalRing.Ideal.IsWeakIdealOfDefinition I}
  ideal I := IdealSheafData.ofSpfOnSpace A hA e I.val I.property
  isWeak I := isWeakIdealOfDefinition_ofSpfOnSpace A hA e I.val I.property
  hasBasis U := ofSpfOnSpace_hasBasis A hA e U

/-- A nonempty family of ideal sheaves that is downward directed on every affine
open is fundamental exactly when it is fundamental on an affine open covering. -/
theorem isFundamentalSystem_iff_affineCover {X : FormalScheme.{u}}
    {ι : Type u} (I : ι → IdealSheafData X)
    (hne : Nonempty ι)
    (hdir : ∀ i j : ι, ∃ k : ι, ∀ U : X.affineOpens,
      (I k).ideal U ≤ (I i).ideal U ∧ (I k).ideal U ≤ (I j).ideal U)
    {κ : Type u} (𝒰 : κ → X.affineOpens) (hcover : ⨆ j, (𝒰 j).1 = ⊤) :
    IsFundamentalSystem I ↔
      ∀ j, IsFundamentalSystemOfWeakIdeals (fun i ↦ (I i).ideal (𝒰 j)) :=
  sorry

/-- Existence of a fundamental system is local on an affine open covering.
A nonempty family fundamental on the cover may be refined by finite intersections. -/
theorem exists_fundamentalSystem_iff_affineCover {X : FormalScheme.{u}}
    {κ : Type u} (𝒰 : κ → X.affineOpens) (hcover : ⨆ j, (𝒰 j).1 = ⊤) :
    Nonempty (FundamentalSystem X) ↔
      ∃ (ι : Type u) (I : ι → IdealSheafData X), Nonempty ι ∧
        ∀ j, TopologicalRing.IsFundamentalSystemOfWeakIdeals
          (fun i ↦ (I i).ideal (𝒰 j)) :=
  sorry

/-- The functor of points `h_X` is a directed colimit of schemes along
thickenings if and only if `X` admits a
fundamental system of weak ideals of definition. -/
theorem exists_fundamentalSystem_iff_isDirectedColimit
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (h𝒮 : Scheme.IsSmallBoundClosed
      (fun T : Scheme.{u} ↦ ∃ U : 𝒮.carrier, Nonempty (T ≅ 𝒮.toScheme.obj U)))
    (X : FormalScheme.{u})
    (hsize : ∃ T : 𝒮.carrier, X.size ≤ (𝒮.toScheme.obj T).size) :
    Nonempty (FundamentalSystem X) ↔
      ∃ (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v))),
        IsDirectedAlgebraicSpaceThickeningColimit D ((sheafOfPoints 𝒮 S).obj X) ∧
          ∀ i : Λ, ∃ Z : Scheme.{u},
            (∃ T : 𝒮.carrier, Z.size ≤ (𝒮.toScheme.obj T).size) ∧
            Nonempty (D.obj i ≅ (sheafOfPoints 𝒮 S).obj (ofScheme.obj Z)) :=
  sorry

end AlgebraicGeometry.McQuillan.FormalScheme
