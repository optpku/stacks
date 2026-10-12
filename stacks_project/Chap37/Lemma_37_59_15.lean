/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.BaseChange
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 37.59.15: Tor-independent base change preserves relative `m`-pseudo-coherence
of a derived module along a locally finite type scheme morphism. -/
@[stacks 09UR]
#check (AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver.pullback :
  ∀ {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (g : S' ⟶ S) {E : RingedSpace.ModuleDerived X.toRingedSpace} {m : ℤ},
    AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver f E m →
      Scheme.TorIndependentOver (Over.mk f) (Over.mk g) →
        AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver (pullback.snd f g)
          ((RingedSpace.modulePullbackDerived (pullback.fst f g).toShHom).obj E) m)
