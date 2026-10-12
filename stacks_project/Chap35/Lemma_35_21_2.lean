/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Dimension
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry

/- Lemma 35.21.2: an étale morphism preserves the local topological Krull dimension at
every source point. -/
@[stacks 04N4] #check (AlgebraicGeometry.Etale.topologicalKrullDimAt_eq :
  ∀ {U V : Scheme.{u}} (f : U ⟶ V) [Etale f] (u : U),
    topologicalKrullDimAt u = topologicalKrullDimAt (f u))

end AlgebraicGeometry
