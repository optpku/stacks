/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Relative.Locality

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 37.58.2 (1): for a locally finite type morphism and a quasicoherent module, relative
finite presentation is equivalent to relative finite presentation of sections on every compatible
affine-open pair. -/
@[stacks 09T7] #check
  (AlgebraicGeometry.Scheme.Modules.isFinitePresentationOver_iff_affineOpenSections :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (F : X.Modules) [F.IsQuasicoherent],
      F.IsFinitePresentationOver f ↔
        ∀ ⦃U : X.Opens⦄, IsAffineOpen U →
          ∀ ⦃V : S.Opens⦄, IsAffineOpen V → ∀ e : U ≤ f ⁻¹ᵁ V,
            @Module.FinitePresentationRelativeTo
              Γ(S, V) Γ(X, U) Γ(F, U) _ _ (Scheme.Hom.sectionsAlgebra f V U e) _ _)

/- Lemma 37.58.2 (2): relative finite presentation of a quasicoherent module is preserved after
restriction to any compatible source and target opens. -/
@[stacks 09T7] #check
  (AlgebraicGeometry.Scheme.Modules.IsFinitePresentationOver.restrict :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (F : X.Modules) [F.IsQuasicoherent], F.IsFinitePresentationOver f →
      ∀ {U : X.Opens} {V : S.Opens} (e : U ≤ f ⁻¹ᵁ V),
        (F.restrict U.ι).IsFinitePresentationOver (f.resLE V U e))

end AlgebraicGeometry.Scheme.Modules
