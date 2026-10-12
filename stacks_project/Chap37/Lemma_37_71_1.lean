/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.PseudoCoherent
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.71.1: if the derived pullback of `K'` along a finite-order thickening
`i : X ⟶ X'` is pseudo-coherent, then `K'` is pseudo-coherent. -/
@[stacks 0DJX] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.isPseudoCoherent_of_pullback :
    ∀ {X X' : AlgebraicGeometry.Scheme.{u}} (i : X ⟶ X')
      [AlgebraicGeometry.IsFiniteOrderThickening i]
      (K' : AlgebraicGeometry.RingedSpace.ModuleDerived X'.toRingedSpace)
      (_ : AlgebraicGeometry.RingedSpace.ModuleDerived.IsPseudoCoherent
        ((AlgebraicGeometry.RingedSpace.modulePullbackDerived i.toShHom).obj K')),
      AlgebraicGeometry.RingedSpace.ModuleDerived.IsPseudoCoherent K')
