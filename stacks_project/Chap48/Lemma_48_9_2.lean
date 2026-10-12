/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.ClosedImmersion.Adjunction
import StacksCheckRecall

/- Lemma 48.9.2: the total right-derived internal-Hom functor from `𝒪_Z` is right
adjoint to derived pushforward `R(i)_*`. -/
@[stacks 0A76] #check (AlgebraicGeometry.RingedSpace.ModuleDerived.ClosedImmersion.adjunction :
  ∀ {X Z : AlgebraicGeometry.RingedSpace} (i : Z ⟶ X)
    (h_closed : Topology.IsClosedEmbedding i.hom.base)
    [CategoryTheory.Sheaf.IsLocallySurjective
      (AlgebraicGeometry.RingedSpace.Hom.commRingSheafPushforwardMap i)],
    AlgebraicGeometry.RingedSpace.moduleDerivedPushforward i ⊣
      AlgebraicGeometry.RingedSpace.ModuleDerived.ClosedImmersion.rHomFromStructureSheaf
        i h_closed)
