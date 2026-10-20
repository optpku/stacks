/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.Flat
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace ModuleDerived
namespace IsMPseudoCoherentOver

/- Lemma 37.70.2: for composable scheme morphisms `X ⟶ T ⟶ S`, with `X ⟶ T`
locally of finite type and `T ⟶ S` flat and locally of finite presentation, a
derived `𝒪_X`-module is `m`-pseudo-coherent over `S` exactly when it is
`m`-pseudo-coherent over `T`. -/
@[stacks 0CSP] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver.comp_iff_of_flat_of_locallyOfFinitePresentation :
    ∀ {X T S : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ S)
      [LocallyOfFiniteType f] [Flat g] [LocallyOfFinitePresentation g]
      (E : RingedSpace.ModuleDerived X.toRingedSpace) (m : ℤ),
      IsMPseudoCoherentOver (f ≫ g) E m ↔ IsMPseudoCoherentOver f E m)

end IsMPseudoCoherentOver
end ModuleDerived
end Scheme
end AlgebraicGeometry
