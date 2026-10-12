/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.RingTheory.Sequence.Koszul.Regularity

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ClosedSubset

/-- A closed subset is locally cut out by Koszul-regular families of exactly `c` sections. -/
def IsKoszulRegularCutout {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X)
    (c : ℕ) : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
    ∃ f : Fin c → Γ(X, U),
      RingTheory.Sequence.IsKoszulRegularSequence f ∧
        X.zeroLocus (Set.range f) = (Z : Set X) ∪ (U : Set X)ᶜ

/-- A closed subset is a Koszul-regular cutout of length `c` exactly when every point has
an affine neighborhood with such a presentation. -/
theorem isKoszulRegularCutout_iff {X : Scheme.{u}}
    (Z : TopologicalSpace.Closeds X) (c : ℕ) :
    IsKoszulRegularCutout Z c ↔
      ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        ∃ f : Fin c → Γ(X, U),
          RingTheory.Sequence.IsKoszulRegularSequence f ∧
            X.zeroLocus (Set.range f) = (Z : Set X) ∪ (U : Set X)ᶜ := sorry

/-- A Koszul-regular cutout of length `c` admits a corresponding affine presentation near
every point. -/
theorem IsKoszulRegularCutout.exists_affine {X : Scheme.{u}}
    {Z : TopologicalSpace.Closeds X} {c : ℕ} (hZ : IsKoszulRegularCutout Z c)
    (x : X) :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
      ∃ f : Fin c → Γ(X, U),
        RingTheory.Sequence.IsKoszulRegularSequence f ∧
          X.zeroLocus (Set.range f) = (Z : Set X) ∪ (U : Set X)ᶜ := sorry

end AlgebraicGeometry.ClosedSubset

end
