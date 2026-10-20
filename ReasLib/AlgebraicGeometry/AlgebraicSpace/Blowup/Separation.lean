/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Admissible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictTransform.Points
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Sets.Closeds

/-!
# Separating open subspaces by admissible blowups

Two disjoint quasi-compact open subspaces of a quasi-compact quasi-separated
algebraic space can be separated by an admissible blowup of their union.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Two disjoint quasi-compact open subspaces of a quasi-compact quasi-separated
algebraic space have disjoint inverse images contained in a two-open cover after
an admissible blowup of their union. -/
theorem exists_isAdmissibleBlowup_disjointOpenCover_of_disjoint_qc_opens
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (U V : OpenSubspace X) [QuasiCompact U.ι] [QuasiCompact V.ι]
    (hUV : Disjoint U.pointsSet V.pointsSet) :
    ∃ (X' : AlgebraicSpace S) (b : X' ⟶ X) (X₁ X₂ : OpenSubspace X'),
      IsAdmissibleBlowup (OpenSubspace.fromOpens (U.pointsOpens ⊔ V.pointsOpens)) b ∧
        Disjoint X₁.pointsSet X₂.pointsSet ∧
          X₁.pointsOpens ⊔ X₂.pointsOpens = ⊤ ∧
            Points.map b ⁻¹' U.pointsSet ⊆ X₁.pointsSet ∧
              Points.map b ⁻¹' V.pointsSet ⊆ X₂.pointsSet :=
  sorry

/-- Two finitely presented closed subspaces whose intersection misses a
quasi-compact open in a quasi-compact quasi-separated algebraic space have
disjoint strict transforms after an admissible blowup over that open. -/
theorem exists_isAdmissibleBlowup_disjointStrictTransforms
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (U : OpenSubspace X) [QuasiCompact U.ι]
    (Z₁ Z₂ : ClosedSubspace X)
    [FinitePresentation Z₁.ι] [FinitePresentation Z₂.ι]
    (h : Disjoint (Z₁.pointsSet ∩ Z₂.pointsSet) U.pointsSet) :
    ∃ (X' : AlgebraicSpace S) (b : X' ⟶ X) (Z : ClosedSubspace X)
      (hZ : IsAdmissibleBlowupCenter U b Z),
      Disjoint (strictTransformPointsSet b Z Z₁)
        (strictTransformPointsSet b Z Z₂) :=
  sorry

/-- Two disjoint constructible closed subsets of a quasi-compact open in a
quasi-compact quasi-separated algebraic space have disjoint closures after an
admissible blowup over that open. -/
theorem exists_isAdmissibleBlowup_disjointConstructibleClosures
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (U : OpenSubspace X) [QuasiCompact U.ι]
    (T₁ T₂ : TopologicalSpace.Closeds (Points U.X))
    (hT₁ : Topology.IsConstructible (T₁ : Set (Points U.X)))
    (hT₂ : Topology.IsConstructible (T₂ : Set (Points U.X)))
    (h : Disjoint (T₁ : Set (Points U.X)) (T₂ : Set (Points U.X))) :
    ∃ (X' : AlgebraicSpace S) (b : X' ⟶ X),
      IsAdmissibleBlowup U b ∧
        Disjoint
          (closure (Points.map b ⁻¹' (Points.map U.ι '' (T₁ : Set (Points U.X)))))
          (closure (Points.map b ⁻¹' (Points.map U.ι '' (T₂ : Set (Points U.X))))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
