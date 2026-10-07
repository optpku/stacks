module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace ModuleDerived
namespace IsMPseudoCoherentOver

/- Lemma 37.59.8: for a morphism of schemes locally of finite type over a base
whose underlying map is a closed embedding, relative `m`-pseudo-coherence is
preserved and reflected by derived pushforward. -/
@[stacks 09VG] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver.iff_pushforward_of_isClosedEmbedding :
    ∀ {X Y S : Scheme.{u}} (i : X ⟶ Y) (g : Y ⟶ S)
      [LocallyOfFiniteType i] [LocallyOfFiniteType g],
      Topology.IsClosedEmbedding i.base → ∀ (E : DerivedCategory X.Modules) (m : ℤ),
        IsMPseudoCoherentOver (i ≫ g) E m ↔
          IsMPseudoCoherentOver g
            ((RingedSpace.moduleDerivedPushforward i.toShHom).obj E) m)

end IsMPseudoCoherentOver
end ModuleDerived
end Scheme
end AlgebraicGeometry
