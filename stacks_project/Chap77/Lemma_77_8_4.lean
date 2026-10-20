/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.Vanishing
import StacksCheckRecall

/-!
# Lemma 77.8.4

For a locally finitely presented algebraic space over an affine scheme and a morphism
of quasi-coherent modules with finitely presented target flat over the base, fibrewise
vanishing on a subset implies vanishing at every point of its closure.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 77.8.4 -/
@[stacks 0CWB]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.baseChangeMap_eq_zero_of_mem_closure :
  ∀ {S : Scheme.{u}} [IsAffine S] {X : AlgebraicSpace S}
    [LocallyOfFinitePresentation (SchemeRealization.toBase X)] {ℱ 𝒢 : X.Modules}
    [ℱ.IsQuasicoherent] [𝒢.IsFinitePresentation]
    (hG_flat : flatOver 𝒢 (SchemeRealization.toBase X)) (u : ℱ ⟶ 𝒢) (T : Set S) {s : S}
    (hs : s ∈ closure T)
    (hT : ∀ t ∈ T, baseChangeMap (SchemeRealization.toBase X) (residueFieldHom S t) u = 0),
    baseChangeMap (SchemeRealization.toBase X) (residueFieldHom S s) u = 0)

end AlgebraicGeometry.AlgebraicSpace.Modules
