/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.UniversallyInjective.CharacterModule.TensorHom
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Remark 35.4.13: a universally injective module morphism induces a split
epimorphism between the corresponding curried character-tensor functors. -/
@[stacks 08WV] #check
  (CharacterModule.TensorHom.isSplitEpi_rightFunctor_map_of_universallyInjective :
    ∀ (R : Type u) [CommRing R] {M N : ModuleCat.{u} R} (f : M ⟶ N),
      LinearMap.UniversallyInjective.{u, u, u, u} f.hom →
        IsSplitEpi ((CharacterModule.TensorHom.rightFunctor R).map f.op))
