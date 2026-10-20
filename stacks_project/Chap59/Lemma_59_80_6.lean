/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Normal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 59.80.6 (1): if `X` is affine, integral, and normal with separably closed
function field, `i : Z ⟶ X` is a closed immersion, and the source of an etale morphism
`f : V ⟶ Z` is affine, then `V` is a finite coproduct of schemes mapping to `Z` by open
immersions. -/
@[stacks 09ZA] #check (AlgebraicGeometry.Scheme.Hom.affineEtale_finiteOpenDecomposition :
    ∀ {X Z V : Scheme.{u}} [IsAffine X] [IsIntegral X] (hX : X.isNormal)
      [IsSepClosed X.functionField] (i : Z ⟶ X) [IsClosedImmersion i]
      [IsAffine V] (f : V ⟶ Z) [Etale f],
    ∃ (n : ℕ) (W : Fin n → Scheme.{u}) (e : V ≅ ∐ W)
      (j : ∀ k, W k ⟶ Z),
      (∀ k, IsOpenImmersion (j k)) ∧ e.hom ≫ Sigma.desc j = f)

/- Lemma 59.80.6 (2): in the same situation, a surjective finite etale morphism
`f : V ⟶ Z` admits a section. -/
@[stacks 09ZA] #check (AlgebraicGeometry.Scheme.Hom.surjectiveFiniteEtale_hasSection :
    ∀ {X Z V : Scheme.{u}} [IsAffine X] [IsIntegral X] (hX : X.isNormal)
      [IsSepClosed X.functionField] (i : Z ⟶ X) [IsClosedImmersion i]
      [IsAffine V] (f : V ⟶ Z) [Surjective f] [IsFinite f] [Etale f],
    ∃ s : Z ⟶ V, s ≫ f = 𝟙 Z)

end AlgebraicGeometry.Scheme.Hom
