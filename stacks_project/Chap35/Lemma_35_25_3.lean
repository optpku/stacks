/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversallyInjective.GenericPoints
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.UniversallyInjective

/- Lemma 35.25.3: A flat separated morphism which induces residue-field isomorphisms at
the generic points of its source and is injective on those generic points is universally
injective. -/
@[stacks 09NP] #check
  (AlgebraicGeometry.UniversallyInjective.of_flat_of_isSeparated_of_genericPoints :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsSeparated f],
      (∀ ξ : X, ξ ∈ genericPoints X → IsIso (f.residueFieldMap ξ)) →
        Set.InjOn f.base (genericPoints X) → UniversallyInjective f)

end AlgebraicGeometry.UniversallyInjective
