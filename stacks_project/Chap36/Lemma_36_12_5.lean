/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

namespace IsMPseudoCoherent

/- Lemma 36.12.5: if `i : Z ⟶ X` is a morphism of ringed spaces whose underlying
continuous map is a closed embedding and `i_* 𝒪_Z` is pseudo-coherent as an
`𝒪_X`-module, then `E ∈ D(𝒪_Z)` is `m`-pseudo-coherent if and only if `R(i)_* E` is
`m`-pseudo-coherent. -/
@[stacks 09VA] #check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent.iff_derivedPushforward_of_isClosedEmbedding :
    {X Z : RingedSpace.{u}} → (i : Z ⟶ X) →
      Topology.IsClosedEmbedding i.hom.base →
      SheafOfModules.IsPseudoCoherent
        ((RingedSpace.Hom.pushforward i).obj
          (SheafOfModules.unit Z.ringCatSheaf : Z.Modules)) →
      (E : ModuleDerived Z) → (m : ℤ) →
        (IsMPseudoCoherent E m ↔
          IsMPseudoCoherent ((RingedSpace.moduleDerivedPushforward i).obj E) m))

end IsMPseudoCoherent

end AlgebraicGeometry.RingedSpace.ModuleDerived
