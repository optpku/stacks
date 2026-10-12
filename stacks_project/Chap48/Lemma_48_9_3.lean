/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ClosedImmersion.InternalHom
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 48.9.3: for a closed immersion `i : Z ⟶ X` of schemes and every
`K : D(O_X)`, derived pushforward of the canonical `RHom(O_Z, K)` is isomorphic
to the canonical ambient `RHom(i_*O_Z, K)` in `D(O_X)`. -/
@[stacks 0A77] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.ClosedImmersion.pushforwardRHomStructureSheaf_isomorphic :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      (K : RingedSpace.ModuleDerived X.toRingedSpace),
      IsIsomorphic
        ((AlgebraicGeometry.RingedSpace.ModuleDerived.ClosedImmersion.pushforwardRHomStructureSheaf
          i.toShHom (IsClosedImmersion.isClosedEmbedding i)).obj K)
        ((AlgebraicGeometry.RingedSpace.ModuleDerived.ClosedImmersion.ambientRHomStructureSheaf
          i.toShHom (IsClosedImmersion.isClosedEmbedding i)).obj K))
