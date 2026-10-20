module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.Retracts
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

/- Lemma 37.59.12: for a locally finite type morphism `f : X ⟶ S`, if `E ⊞ K`
is relatively `m`-pseudo-coherent over `S`, then both `E` and `K` are relatively
`m`-pseudo-coherent over `S`. -/
@[stacks 09UN] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver.summands :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (E K : RingedSpace.ModuleDerived X.toRingedSpace) {m : ℤ},
      AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver f (E ⊞ K) m →
        AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver f E m ∧
          AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver f K m)
