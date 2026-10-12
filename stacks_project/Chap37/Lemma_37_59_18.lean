/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

/- Lemma 37.59.18: for a closed immersion `i : X ⟶ P` and a flat morphism
`p : P ⟶ S` locally of finite presentation, relative `m`-pseudo-coherence of `E`,
relative `m`-pseudo-coherence of its derived pushforward, and absolute
`m`-pseudo-coherence of that pushforward are equivalent. -/
@[stacks 09UU] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.mPseudoCoherent_pushforward_tfae :
    ∀ {X P S : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S)
      [IsClosedImmersion i] [Flat p] [LocallyOfFinitePresentation p]
      (E : RingedSpace.ModuleDerived X.toRingedSpace) (m : ℤ),
      List.TFAE [
        IsMPseudoCoherentOver (i ≫ p) E m,
        IsMPseudoCoherentOver p
          ((RingedSpace.moduleDerivedPushforward i.toShHom).obj E) m,
        RingedSpace.ModuleDerived.IsMPseudoCoherent
          ((RingedSpace.moduleDerivedPushforward i.toShHom).obj E) m
      ])

end ModuleDerived
end Scheme
end AlgebraicGeometry
