/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.DescentLocus
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 37.33.2: a finite locally free module on a flat proper finitely presented
scheme over a reduced base descends to a finite locally free module on the base if
the structure-sheaf unit remains an isomorphism after every base change and every
fiber restriction is finite free. -/
@[stacks 0EX7] #check
  (AlgebraicGeometry.Scheme.Modules.existsPullbackOfFiniteFreeFibers :
    ∀ {X S : Scheme.{u}} [IsReduced S]
      (f : X ⟶ S) [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
      (E : X.Modules) [E.IsFiniteLocallyFree],
      (∀ {T : Scheme.{u}} (g : T ⟶ S),
        IsIso (SheafOfModules.unitToPushforwardObjUnit
          (pullback.snd f g).toRingCatSheafHom)) →
      (∀ s : S, SheafOfModules.IsFiniteFree
        ((Scheme.Modules.pullback (f.fiberι s)).obj E)) →
      ∃ (N : S.Modules) (_ : N.IsFiniteLocallyFree),
        Nonempty ((Scheme.Modules.pullback f).obj N ≅ E))

end AlgebraicGeometry.Scheme.Modules
