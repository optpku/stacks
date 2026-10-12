/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace AlgebraicGeometry
namespace Scheme
namespace ModuleDerived
namespace IsMPseudoCoherentOver

/- Lemma 37.70.3: for a locally finite type morphism `f : X ⟶ S` and an fppf cover
`𝒰` of `S`, a derived quasi-coherent complex `E` is relatively `m`-pseudo-coherent
over `S` if and only if its derived pullback to every base change along `𝒰` is
relatively `m`-pseudo-coherent over the corresponding member of the cover. -/
@[stacks 0CSQ] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver.iff_fppfCover_target :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (𝒰 : FppfCover.{u, v} S) (E : Scheme.DerivedQCoh X) (m : ℤ),
      IsMPseudoCoherentOver f E.obj m ↔
        ∀ i : 𝒰.I₀, IsMPseudoCoherentOver (pullback.snd f (𝒰.f i))
          ((Scheme.DerivedQCoh.pullback (pullback.fst f (𝒰.f i))).obj E).obj m)

end IsMPseudoCoherentOver
end ModuleDerived
end Scheme
end AlgebraicGeometry
