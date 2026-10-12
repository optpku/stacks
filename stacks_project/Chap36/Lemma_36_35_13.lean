/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative.Fiber
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 36.35.13: for a flat, locally finitely presented morphism `f : X ⟶ S` and a
pseudo-coherent derived `𝒪_X`-module `E`, relative perfectness is equivalent to local
boundedness below of `E` and of its derived pullback to every scheme-theoretic fiber. -/
@[stacks 0GEH] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.isPerfectRelativeTo_iff_locallyBoundedBelow_and_fiber :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Flat f] [AlgebraicGeometry.LocallyOfFinitePresentation f]
      (E : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace)
      (_ : AlgebraicGeometry.RingedSpace.ModuleDerived.IsPseudoCoherent E),
        AlgebraicGeometry.Scheme.ModuleDerived.IsPerfectRelativeTo f E ↔
          AlgebraicGeometry.RingedSpace.ModuleDerived.IsLocallyBoundedBelow E ∧
            ∀ s : S, AlgebraicGeometry.RingedSpace.ModuleDerived.IsLocallyBoundedBelow
              ((AlgebraicGeometry.RingedSpace.modulePullbackDerived
                (f.fiberι s).toShHom).obj E))
