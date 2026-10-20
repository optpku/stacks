/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Derivation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 51.19.3: a quasi-compact, quasi-separated, étale morphism
`f : V ⟶ Spec (CommRingCat.of A)` admits, for every absolute derivation `θ` and degree `i`,
a canonical additive operator on `H^i(V, 𝒪_V)` satisfying the `θ`-Leibniz rule. -/
@[stacks 0EC7]
#check (AlgebraicGeometry.Scheme.Hom.existsCohomologyDerivationOperator :
  ∀ {A : Type u} [CommRing A] {V : Scheme.{u}}
    (f : V ⟶ Spec (CommRingCat.of A))
    [QuasiCompact f] [QuasiSeparated f] [Etale f]
    (θ : Derivation ℤ A A) (i : ℕ),
    ∃ D : Module.End ℤ
        (AlgebraicGeometry.Scheme.Hom.cohomology f
          (SheafOfModules.unit V.ringCatSheaf : V.Modules) i),
      D.IsModuleDerivation θ)
