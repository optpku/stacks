/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.QuasiIso
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Two-out-of-three for quasi-isomorphisms of distinguished triangles

This leaf isolates the homotopy-category fact used by Mayer--Vietoris arguments.  The
source-facing chapter entry recalls this API; no site, sheaf, or chosen resolution occurs here.
-/

open CategoryTheory CategoryTheory.Pretriangulated
open ComplexShape HomotopyCategory

universe w v u

namespace CategoryTheory.Pretriangulated.TriangleMorphism

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- Lemma 21.26.2 (0EWP): for a morphism of distinguished triangles in `K(𝒜)`,
quasi-isomorphisms satisfy two-out-of-three on the three triangle components. -/
@[stacks 0EWP "quasi-isomorphism two-out-of-three for distinguished triangles"]
theorem quasiIso_two_out_of_three
    {T T' : Triangle (HomotopyCategory 𝒜 (up ℤ))} (φ : T ⟶ T')
    (hT : T ∈ distTriang (HomotopyCategory 𝒜 (up ℤ)))
    (hT' : T' ∈ distTriang (HomotopyCategory 𝒜 (up ℤ))) :
    (quasiIso 𝒜 (up ℤ) φ.hom₁ ∧ quasiIso 𝒜 (up ℤ) φ.hom₂ →
        quasiIso 𝒜 (up ℤ) φ.hom₃) ∧
      (quasiIso 𝒜 (up ℤ) φ.hom₁ ∧ quasiIso 𝒜 (up ℤ) φ.hom₃ →
        quasiIso 𝒜 (up ℤ) φ.hom₂) ∧
      (quasiIso 𝒜 (up ℤ) φ.hom₂ ∧ quasiIso 𝒜 (up ℤ) φ.hom₃ →
        quasiIso 𝒜 (up ℤ) φ.hom₁) := sorry

/-- The third component of a distinguished-triangle morphism is a quasi-isomorphism when the
first two components are. -/
@[stacks 0EWP "third component from the first two"]
theorem quasiIso₃_of_quasiIso₁₂
    {T T' : Triangle (HomotopyCategory 𝒜 (up ℤ))} (φ : T ⟶ T')
    (hT : T ∈ distTriang (HomotopyCategory 𝒜 (up ℤ)))
    (hT' : T' ∈ distTriang (HomotopyCategory 𝒜 (up ℤ)))
    (h₁ : quasiIso 𝒜 (up ℤ) φ.hom₁) (h₂ : quasiIso 𝒜 (up ℤ) φ.hom₂) :
    quasiIso 𝒜 (up ℤ) φ.hom₃ := sorry

/-- The second component of a distinguished-triangle morphism is a quasi-isomorphism when the
first and third components are. -/
@[stacks 0EWP "second component from the outer components"]
theorem quasiIso₂_of_quasiIso₁₃
    {T T' : Triangle (HomotopyCategory 𝒜 (up ℤ))} (φ : T ⟶ T')
    (hT : T ∈ distTriang (HomotopyCategory 𝒜 (up ℤ)))
    (hT' : T' ∈ distTriang (HomotopyCategory 𝒜 (up ℤ)))
    (h₁ : quasiIso 𝒜 (up ℤ) φ.hom₁) (h₃ : quasiIso 𝒜 (up ℤ) φ.hom₃) :
    quasiIso 𝒜 (up ℤ) φ.hom₂ := sorry

/-- The first component of a distinguished-triangle morphism is a quasi-isomorphism when the
second and third components are. -/
@[stacks 0EWP "first component from the last two"]
theorem quasiIso₁_of_quasiIso₂₃
    {T T' : Triangle (HomotopyCategory 𝒜 (up ℤ))} (φ : T ⟶ T')
    (hT : T ∈ distTriang (HomotopyCategory 𝒜 (up ℤ)))
    (hT' : T' ∈ distTriang (HomotopyCategory 𝒜 (up ℤ)))
    (h₂ : quasiIso 𝒜 (up ℤ) φ.hom₂) (h₃ : quasiIso 𝒜 (up ℤ) φ.hom₃) :
    quasiIso 𝒜 (up ℤ) φ.hom₁ := sorry

end CategoryTheory.Pretriangulated.TriangleMorphism

end
