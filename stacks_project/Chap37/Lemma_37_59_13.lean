module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.BoundedAbove
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace ModuleDerived
namespace IsMPseudoCoherentOver

/- Lemma 37.59.13: a locally bounded-above complex whose degree-`i` term is relatively
`(m - i)`-pseudo-coherent determines a relatively `m`-pseudo-coherent derived module. -/
@[stacks 09UP] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver.of_locallyBoundedAbove_of_termwise :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S), [LocallyOfFiniteType f] →
      ∀ (K : CochainComplex X.Modules ℤ) (m : ℤ),
        RingedSpace.CochainComplex.IsLocallyBoundedAbove K →
          (∀ i : ℤ, (K.X i).IsMPseudoCoherentOver f (m - i)) →
            IsMPseudoCoherentOver f (DerivedCategory.Q.obj K) m)

end IsMPseudoCoherentOver
end ModuleDerived
end Scheme
end AlgebraicGeometry
