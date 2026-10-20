/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/- Lemma 29.10.2
Universal injectivity, injectivity on field-valued points, radiciality, and
surjectivity of the diagonal are equivalent. The third entry expands
radiciality as injectivity on points together with purely inseparable residue
field extensions. -/
@[stacks 01S4] #check
  (AlgebraicGeometry.tfae_universallyInjective f :
    List.TFAE [
      UniversallyInjective f,
      ∀ (K : Type u) [Field K], Function.Injective (fun g : Spec (.of K) ⟶ X ↦ g ≫ f),
      Function.Injective f ∧ ∀ x, (f.residueFieldMap x).hom.IsPurelyInseparable,
      Surjective (pullback.diagonal f)])

end AlgebraicGeometry
