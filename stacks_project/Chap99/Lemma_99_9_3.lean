/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap99.Lemma_99_9_3_SpacePoint
public import stacks_project.Chap99.Lemma_99_9_3_Sheaf

/-!
# Lemma 99.9.3

In Situation 99.9.1, morphisms of fppf sheaves from an algebraic space `T` over
`S` into `Hilb_{X/B}` are identified with pairs `(h, Z)` where `h : T ⟶ B` and
`Z ⊂ X_T = X ×_{B,h} T` is a closed subspace such that `Z ⟶ T` is of finite
presentation, flat, and proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 99.9.3: in Situation 99.9.1, let `T` be an algebraic space over `S`.
Morphisms of fppf sheaves `T ⟶ Hilb_{X/B}` on `(Sch/S)_fppf` are in bijection
with pairs `(h, Z)` where `h : T ⟶ B` and `Z ⊂ X_T = X ×_{B,h} T` is a closed
subspace such that `Z ⟶ T` is of finite presentation, flat, and proper,
identified by ideal sheaves. -/
@[stacks 0D3W]
theorem hilbertSheafHom_bijective (f : X ⟶ B) [FinitePresentation f]
    (T : AlgebraicSpace S) :
    Function.Bijective (toHilbertSheafHom f T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hilbert
