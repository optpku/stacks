/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Cohomology
public import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 07MC

# Boundary morphisms and cohomology products

This file records the sign relating the two connecting morphisms attached to compatible pairings
of short exact sequences of cochain complexes.  The cohomology products are explicit morphisms;
`CohomologyCup.IsInducedTo` records that they descend from the given chain-level pairings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open ComplexShape

noncomputable section

universe u v

namespace HomologicalComplex.CohomologyCup

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
variable [MonoidalPreadditive C]
variable {SF SG : ShortComplex (CochainComplex C ℤ)} {H : CochainComplex C ℤ}
variable [HasTensor SF.X₁ SG.X₂] [HasTensor SF.X₂ SG.X₂]
variable [HasTensor SF.X₁ SG.X₃] [HasTensor SF.X₂ SG.X₁]
variable [HasTensor SF.X₃ SG.X₁]

/-- Algebraic core of Lemma 20.25.4 (07MC): for compatible pairings of two short exact sequences
of cochain complexes, applying the first connecting morphism before the induced cohomology product
agrees with applying the second connecting morphism, up to the Koszul sign `(-1)^(n + 1)`.
The epimorphism hypothesis is local to the two degrees: the canonical cocycle pullback covers,
followed by the homology quotients, jointly allow the chain-level calculation to descend to
cohomology. It does not require tensoring to preserve every epimorphism. -/
@[stacks 07MC "algebraic boundary-cup compatibility"]
theorem boundary (hF : SF.ShortExact) (hG : SG.ShortExact)
    (γ₁ : tensorObj SF.X₁ SG.X₃ ⟶ H) (γ₂ : tensorObj SF.X₂ SG.X₂ ⟶ H)
    (γ₃ : tensorObj SF.X₃ SG.X₁ ⟶ H)
    (hγ₁ : CommSq (tensorHom (𝟙 SF.X₁) SG.g) (tensorHom SF.f (𝟙 SG.X₂)) γ₁ γ₂)
    (hγ₃ : CommSq (tensorHom SF.g (𝟙 SG.X₁)) (tensorHom (𝟙 SF.X₂) SG.f) γ₃ γ₂)
    (n m : ℤ)
    [Epi ((pullback.snd (SF.g.f n) (SF.X₃.iCycles n) ≫ SF.X₃.homologyπ n) ⊗ₘ
      (pullback.snd (SG.g.f m) (SG.X₃.iCycles m) ≫ SG.X₃.homologyπ m))]
    (cup₁ : SF.X₁.homology (n + 1) ⊗ SG.X₃.homology m ⟶ H.homology (n + m + 1))
    (cup₃ : SF.X₃.homology n ⊗ SG.X₁.homology (m + 1) ⟶ H.homology (n + m + 1))
    (hcup₁ : IsInducedTo γ₁ (n + 1) m (n + m + 1) (add_right_comm n 1 m) cup₁)
    (hcup₃ : IsInducedTo γ₃ n (m + 1) (n + m + 1) (add_assoc n m 1).symm cup₃) :
    ((hF.δ n (n + 1) rfl) ▷ SG.X₃.homology m) ≫ cup₁ =
      (n + 1).negOnePow • ((SF.X₃.homology n ◁ hG.δ m (m + 1) rfl) ≫ cup₃) := sorry

end HomologicalComplex.CohomologyCup

end
