/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.InfinitesimalNeighbourhood
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom
namespace InfinitesimalNeighbourhood

/- Lemma 37.5.3: for an immersion, the canonical conormal morphism from the conormal sheaf
in the ambient scheme to the conormal sheaf in its first-order infinitesimal neighbourhood is
an isomorphism. -/
@[stacks 04F0]
#check (AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood.conormalComparison_isIso :
  ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i],
    IsIso (Conormal.factorizationConormalComparison i (fromSource i 1) (toAmbient i 1)
      (fromSource_toAmbient i 1)))

end InfinitesimalNeighbourhood
end Hom
end Scheme
end AlgebraicGeometry
