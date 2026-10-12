/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.Homology
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.59.14: a locally bounded-above derived `𝒪_X`-module whose homology in
degree `i` is `(m - i)`-pseudo-coherent over `S` is `m`-pseudo-coherent over `S`. -/
@[stacks 09UQ] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver.of_homology :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.LocallyOfFiniteType f]
      (E : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace) (m : ℤ)
      (hE : E.IsLocallyBoundedAbove)
      (hH : ∀ i : ℤ,
        ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsMPseudoCoherentOver f (m - i)),
      AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver f E m)
