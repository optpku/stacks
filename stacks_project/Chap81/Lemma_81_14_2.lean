/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Separation
import StacksCheckRecall

/-!
# Separating finitely presented closed subspaces by admissible blowups

On a quasi-compact quasi-separated algebraic space, finitely presented closed
subspaces that miss a quasi-compact open become disjoint after a `U`-admissible
blowup, as do the closures of disjoint constructible closed subsets of `|U|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 81.14.2 (1). Let `S` be a scheme. Let `X` be a quasi-compact and
quasi-separated algebraic space over `S`. Let `U ⊂ X` be a quasi-compact open.
If `Z₁, Z₂ ⊂ X` are closed subspaces of finite presentation such that
`Z₁ ∩ Z₂ ∩ U = ∅`, then there exists a `U`-admissible blowing up `X' ⟶ X`
such that the strict transforms of `Z₁` and `Z₂` are disjoint. -/
@[stacks 0F46] #check (AlgebraicGeometry.AlgebraicSpace.exists_isAdmissibleBlowup_disjointStrictTransforms :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (U : OpenSubspace X) [QuasiCompact U.ι]
    (Z₁ Z₂ : ClosedSubspace X)
    [FinitePresentation Z₁.ι] [FinitePresentation Z₂.ι]
    (h : Disjoint (Z₁.pointsSet ∩ Z₂.pointsSet) U.pointsSet),
    ∃ (X' : AlgebraicSpace S) (b : X' ⟶ X) (Z : ClosedSubspace X)
      (hZ : IsAdmissibleBlowupCenter U b Z),
      Disjoint (strictTransformPointsSet b Z Z₁)
        (strictTransformPointsSet b Z Z₂))

/- Lemma 81.14.2 (2). Let `S` be a scheme. Let `X` be a quasi-compact and
quasi-separated algebraic space over `S`. Let `U ⊂ X` be a quasi-compact open.
If `T₁, T₂ ⊂ |U|` are disjoint constructible closed subsets, then there is a
`U`-admissible blowing up `X' ⟶ X` such that the closures of `T₁` and `T₂`
are disjoint. -/
@[stacks 0F46] #check (AlgebraicGeometry.AlgebraicSpace.exists_isAdmissibleBlowup_disjointConstructibleClosures :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (U : OpenSubspace X) [QuasiCompact U.ι]
    (T₁ T₂ : TopologicalSpace.Closeds (Points U.X))
    (hT₁ : Topology.IsConstructible (T₁ : Set (Points U.X)))
    (hT₂ : Topology.IsConstructible (T₂ : Set (Points U.X)))
    (h : Disjoint (T₁ : Set (Points U.X)) (T₂ : Set (Points U.X))),
    ∃ (X' : AlgebraicSpace S) (b : X' ⟶ X),
      IsAdmissibleBlowup U b ∧
        Disjoint
          (closure (Points.map b ⁻¹' (Points.map U.ι '' (T₁ : Set (Points U.X)))))
          (closure (Points.map b ⁻¹' (Points.map U.ι '' (T₂ : Set (Points U.X))))))

end AlgebraicGeometry.AlgebraicSpace
