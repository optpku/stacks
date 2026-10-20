/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Derivation.Affine

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 29.32.4: for a ring map `φ : R ⟶ A` and an `𝒪_{Spec A}`-module sheaf `ℱ`,
taking the action of a relative sheaf derivation on global sections is a bijection onto the
`R`-derivations of the module of global sections. -/
@[stacks 01UO] #check (AlgebraicGeometry.Scheme.Modules.AffineDerivation.globalSections_bijective :
    ∀ {R A : CommRingCat.{u}} (φ : R ⟶ A) (ℱ : (Spec A).Modules),
      Function.Bijective
        (AlgebraicGeometry.Scheme.Modules.AffineDerivation.globalSections φ ℱ))
