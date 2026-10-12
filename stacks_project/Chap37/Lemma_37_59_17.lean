/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.59.17: for locally finite type morphisms `X ⟶ Y ⟶ S`, if `Y ⟶ S` is
pseudo-coherent, then a derived `𝒪_X`-module is `m`-pseudo-coherent over `Y` exactly when
it is `m`-pseudo-coherent over `S`. -/
@[stacks 09UT]
#check
  (AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver.iff_comp :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
      [AlgebraicGeometry.LocallyOfFiniteType f] [AlgebraicGeometry.LocallyOfFiniteType g]
      [AlgebraicGeometry.PseudoCoherent g]
      (E : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace) (m : ℤ),
      AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver f E m ↔
        AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver (f ≫ g) E m)
