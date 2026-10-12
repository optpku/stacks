/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.OpenImmersion.GenericPoints
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 33.42.1: A separated morphism which is locally an open immersion on its source and is
injective on the generic points of its source is an open immersion. -/
@[stacks 09NG] #check
  (AlgebraicGeometry.IsOpenImmersion.of_openCover_source_of_injOn_genericPoints :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f],
      (∃ 𝒰 : X.OpenCover, ∀ i, IsOpenImmersion (𝒰.f i ≫ f)) →
        Set.InjOn f.base (genericPoints X) → IsOpenImmersion f)
