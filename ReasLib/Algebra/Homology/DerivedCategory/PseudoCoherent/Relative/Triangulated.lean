/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Derived
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Triangulated
import Mathlib.Tactic.CrossRefAttribute

/-!
# Triangles of relatively pseudo-coherent derived objects

The presentationwise relative predicates inherit the shifted two-out-of-three behavior of
absolute pseudo-coherence after restriction to each polynomial presentation.

@stack 0674
-/

@[expose] public section

noncomputable section

open CategoryTheory ObjectProperty Pretriangulated

universe u v

namespace CategoryTheory.DerivedCategory

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]

local notation "DModA" => DerivedCategory (ModuleCat A)

namespace IsMPseudoCoherentRelativeTo

/-- Shifting a relatively `m`-pseudo-coherent object translates the bound by the shift. -/
@[stacks 0674 "relative pseudo-coherence under shifts"]
theorem shift_iff (K : DModA) (n m : ℤ) :
    (K⟦n⟧).IsMPseudoCoherentRelativeTo R (m - n) ↔
      K.IsMPseudoCoherentRelativeTo R m := sorry

/-- Lemma 15.82.6 (1): the third vertex inherits the indicated relative pseudo-coherence
bound. -/
@[stacks 0674 "(1), third vertex"]
theorem obj₃ {m : ℤ} (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₁ : T.obj₁.IsMPseudoCoherentRelativeTo R (m + 1))
    (h₂ : T.obj₂.IsMPseudoCoherentRelativeTo R m) :
    T.obj₃.IsMPseudoCoherentRelativeTo R m := sorry

/-- Lemma 15.82.6 (2): the middle vertex inherits the common relative pseudo-coherence
bound. -/
@[stacks 0674 "(2), middle vertex"]
theorem obj₂ {m : ℤ} (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₁ : T.obj₁.IsMPseudoCoherentRelativeTo R m)
    (h₃ : T.obj₃.IsMPseudoCoherentRelativeTo R m) :
    T.obj₂.IsMPseudoCoherentRelativeTo R m := sorry

/-- Lemma 15.82.6 (3): the first vertex inherits the shifted relative pseudo-coherence
bound. -/
@[stacks 0674 "(3), first vertex"]
theorem obj₁ {m : ℤ} (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₂ : T.obj₂.IsMPseudoCoherentRelativeTo R (m + 1))
    (h₃ : T.obj₃.IsMPseudoCoherentRelativeTo R m) :
    T.obj₁.IsMPseudoCoherentRelativeTo R (m + 1) := sorry

/-- Relative `m`-pseudo-coherence is invariant under isomorphism. -/
@[stacks 0674 "relative m-pseudo-coherence isomorphism invariance"]
instance isClosedUnderIsomorphisms (m : ℤ) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun K : DModA ↦ K.IsMPseudoCoherentRelativeTo R m) := sorry

/-- For fixed `m`, relatively `m`-pseudo-coherent objects satisfy two-out-of-three for
distinguished triangles. -/
@[stacks 0674 "relative m-pseudo-coherence triangle closure"]
instance isTriangulatedClosed₂ (m : ℤ) :
    ObjectProperty.IsTriangulatedClosed₂
      (fun K : DModA ↦ K.IsMPseudoCoherentRelativeTo R m) := sorry

end IsMPseudoCoherentRelativeTo

namespace IsPseudoCoherentRelativeTo

/-- Relative pseudo-coherence is invariant under isomorphism. -/
@[stacks 0674 "relative pseudo-coherence isomorphism invariance"]
instance isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun K : DModA ↦ K.IsPseudoCoherentRelativeTo R) := sorry

/-- Relatively pseudo-coherent objects form a triangulated object property. -/
@[stacks 0674 "relative pseudo-coherence triangulated property"]
instance isTriangulated :
    ObjectProperty.IsTriangulated
      (fun K : DModA ↦ K.IsPseudoCoherentRelativeTo R) := sorry

/-- Lemma 15.82.6 (4): the third vertex is relatively pseudo-coherent when the first two
vertices are. -/
@[stacks 0674 "(4), third vertex"]
theorem obj₃ (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₁ : T.obj₁.IsPseudoCoherentRelativeTo R)
    (h₂ : T.obj₂.IsPseudoCoherentRelativeTo R) :
    T.obj₃.IsPseudoCoherentRelativeTo R := sorry

/-- Lemma 15.82.6 (5): the middle vertex is relatively pseudo-coherent when the first and third
vertices are. -/
@[stacks 0674 "(5), middle vertex"]
theorem obj₂ (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₁ : T.obj₁.IsPseudoCoherentRelativeTo R)
    (h₃ : T.obj₃.IsPseudoCoherentRelativeTo R) :
    T.obj₂.IsPseudoCoherentRelativeTo R := sorry

/-- Lemma 15.82.6 (6): the first vertex is relatively pseudo-coherent when the middle and third
vertices are. -/
@[stacks 0674 "(6), first vertex"]
theorem obj₁ (T : Triangle DModA) (hT : T ∈ distTriang DModA)
    (h₂ : T.obj₂.IsPseudoCoherentRelativeTo R)
    (h₃ : T.obj₃.IsPseudoCoherentRelativeTo R) :
    T.obj₁.IsPseudoCoherentRelativeTo R := sorry

end IsPseudoCoherentRelativeTo

end CategoryTheory.DerivedCategory
