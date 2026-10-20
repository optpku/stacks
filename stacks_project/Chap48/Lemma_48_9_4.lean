module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.ClosedImmersion.InternalHom
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped CartesianClosed

noncomputable section

universe u

/- Lemma 48.9.4: for a closed-subspace morphism `i : Z ⟶ X`, derived internal Hom from
`R(i)_* M` to `K` is isomorphic to the derived pushforward of the internal Hom from `M` to the
canonical derived Hom from the structure sheaf. -/
@[stacks 0E2I] #check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.ClosedImmersion.pushforward_internalHom_isomorphic :
    ∀ {X Z : RingedSpace.{u}} (i : Z ⟶ X)
      (h_closed : Topology.IsClosedEmbedding i.hom.base)
      [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)]
      [MonoidalCategory (RingedSpace.ModuleDerived X)]
      [MonoidalClosed (RingedSpace.ModuleDerived X)]
      [MonoidalCategory (RingedSpace.ModuleDerived Z)]
      [MonoidalClosed (RingedSpace.ModuleDerived Z)]
      (M : RingedSpace.ModuleDerived Z) (K : RingedSpace.ModuleDerived X),
      IsIsomorphic
        (((RingedSpace.moduleDerivedPushforward i).obj M) ⟹ K)
        ((RingedSpace.moduleDerivedPushforward i).obj
          (M ⟹
            (AlgebraicGeometry.RingedSpace.ModuleDerived.ClosedImmersion.rHomFromStructureSheaf
              i h_closed).obj K)))
