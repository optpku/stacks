/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Triangles of pseudo-coherent derived modules

For a fixed degree, pseudo-coherence has the shifted two-out-of-three behavior expected from
bounded finite-free approximations.  The API is attached to the canonical
`DerivedCategory.IsMPseudoCoherent` predicate, independently of the proof model used to establish
the approximation theorem.

@stack 064R
-/

@[expose] public section

noncomputable section

open CategoryTheory ObjectProperty Pretriangulated

universe u

namespace CategoryTheory.DerivedCategory.IsMPseudoCoherent

variable {R : Type u} [Ring R]

/-- Shifting by `n` translates the pseudo-coherence bound by `n`. -/
theorem shift {K : DerivedCategory (ModuleCat R)} {m : ℤ}
    (hK : K.IsMPseudoCoherent m) (n : ℤ) :
    (K⟦n⟧).IsMPseudoCoherent (m - n) := sorry

/-- Pseudo-coherence after a shift is equivalent to pseudo-coherence with the translated bound. -/
@[stacks 064R "shifted pseudo-coherence"]
theorem shift_iff (K : DerivedCategory (ModuleCat R)) (n m : ℤ) :
    (K⟦n⟧).IsMPseudoCoherent (m - n) ↔ K.IsMPseudoCoherent m := sorry

/-- Lemma 15.65.2 (1): the third vertex inherits the indicated pseudo-coherence bound. -/
@[stacks 064R "(1)"]
theorem obj₃ {m : ℤ} (T : Triangle (DerivedCategory (ModuleCat R)))
    (hT : T ∈ distTriang (DerivedCategory (ModuleCat R)))
    (h₁ : T.obj₁.IsMPseudoCoherent (m + 1))
    (h₂ : T.obj₂.IsMPseudoCoherent m) :
    T.obj₃.IsMPseudoCoherent m := sorry

/-- Lemma 15.65.2 (2): the middle vertex inherits the common pseudo-coherence bound. -/
@[stacks 064R "(2)"]
theorem obj₂ {m : ℤ} (T : Triangle (DerivedCategory (ModuleCat R)))
    (hT : T ∈ distTriang (DerivedCategory (ModuleCat R)))
    (h₁ : T.obj₁.IsMPseudoCoherent m)
    (h₃ : T.obj₃.IsMPseudoCoherent m) :
    T.obj₂.IsMPseudoCoherent m := sorry

/-- Lemma 15.65.2 (3): the first vertex inherits the shifted pseudo-coherence bound. -/
@[stacks 064R "(3)"]
theorem obj₁ {m : ℤ} (T : Triangle (DerivedCategory (ModuleCat R)))
    (hT : T ∈ distTriang (DerivedCategory (ModuleCat R)))
    (h₂ : T.obj₂.IsMPseudoCoherent (m + 1))
    (h₃ : T.obj₃.IsMPseudoCoherent m) :
    T.obj₁.IsMPseudoCoherent (m + 1) := sorry

/-- For fixed `m`, `m`-pseudo-coherent objects satisfy the two-out-of-three property for
distinguished triangles. -/
@[stacks 064R "m-pseudo-coherent objects satisfy two-out-of-three"]
instance isTriangulatedClosed₂ (m : ℤ) :
    IsTriangulatedClosed₂
      (fun K : DerivedCategory (ModuleCat R) ↦ K.IsMPseudoCoherent m) := sorry

end CategoryTheory.DerivedCategory.IsMPseudoCoherent

namespace CategoryTheory.DerivedCategory.IsPseudoCoherent

variable {R : Type u} [Ring R]

/-- Lemma 15.65.6: pseudo-coherence is equivalent to `m`-pseudo-coherence in every degree. -/
@[stacks 064V "pseudo-coherence detected degreewise"]
theorem iff_forall_isMPseudoCoherent
    (K : DerivedCategory (ModuleCat R)) :
    K.IsPseudoCoherent ↔ ∀ m : ℤ, K.IsMPseudoCoherent m := sorry

/-- Pseudo-coherent derived module objects form a triangulated object property. -/
@[stacks 064V "triangulated pseudo-coherent objects"]
instance isTriangulated :
    ObjectProperty.IsTriangulated
      (fun K : DerivedCategory (ModuleCat R) ↦ K.IsPseudoCoherent) := sorry

/-- Lemma 15.65.6 (1): the third vertex of a distinguished triangle is pseudo-coherent when the
first two vertices are. -/
@[stacks 064V "(1), third vertex"]
theorem obj₃
    (T : Triangle (DerivedCategory (ModuleCat R))) (hT : T ∈ distTriang _)
    (h₁ : T.obj₁.IsPseudoCoherent) (h₂ : T.obj₂.IsPseudoCoherent) :
    T.obj₃.IsPseudoCoherent := sorry

/-- Lemma 15.65.6 (2): the middle vertex of a distinguished triangle is pseudo-coherent when the
first and third vertices are. -/
@[stacks 064V "(2), middle vertex"]
theorem obj₂
    (T : Triangle (DerivedCategory (ModuleCat R))) (hT : T ∈ distTriang _)
    (h₁ : T.obj₁.IsPseudoCoherent) (h₃ : T.obj₃.IsPseudoCoherent) :
    T.obj₂.IsPseudoCoherent := sorry

/-- Lemma 15.65.6 (3): the first vertex of a distinguished triangle is pseudo-coherent when the
middle and third vertices are. -/
@[stacks 064V "(3), first vertex"]
theorem obj₁
    (T : Triangle (DerivedCategory (ModuleCat R))) (hT : T ∈ distTriang _)
    (h₂ : T.obj₂.IsPseudoCoherent) (h₃ : T.obj₃.IsPseudoCoherent) :
    T.obj₁.IsPseudoCoherent := sorry

end CategoryTheory.DerivedCategory.IsPseudoCoherent
