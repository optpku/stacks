module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ClosedImmersion
import StacksCheckRecall

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

/- Lemma 59.46.3 (1): for a closed immersion `i : Z ⟶ X`, the stalk of the
small-étale pushforward of `G` at a geometric point outside `Set.range i.base`
is equivalent to the singleton type `PUnit`. -/
@[stacks 04FX] #check (AlgebraicGeometry.Scheme.Etale.stalk_pushforward_closedImmersion_outside :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      (G : Sheaf Z.smallEtaleTopology (Type u)) (xbar : Scheme.GeometricPoint X),
    xbar.image ∉ Set.range i.base →
    Nonempty
      (Scheme.Etale.stalk xbar
          (((Scheme.smallEtalePullback i).sheafPushforwardContinuous
              (Type u) X.smallEtaleTopology Z.smallEtaleTopology).obj G).1 ≃
        PUnit))

/- Lemma 59.46.3 (2): for a closed immersion `i : Z ⟶ X`, a chosen lift
`s : Spec (.of xbar.K) ⟶ Z` identifies the pushed-forward stalk at `xbar`
with the stalk of `G` at the induced geometric point of `Z`. -/
@[stacks 04FX] #check (AlgebraicGeometry.Scheme.Etale.stalk_pushforward_closedImmersion_inside :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      (G : Sheaf Z.smallEtaleTopology (Type u)) (xbar : Scheme.GeometricPoint X),
    xbar.image ∈ Set.range i.base →
    ∀ (s : Spec (.of xbar.K) ⟶ Z), s ≫ i = xbar.hom →
    Nonempty
      (Scheme.Etale.stalk xbar
          (((Scheme.smallEtalePullback i).sheafPushforwardContinuous
              (Type u) X.smallEtaleTopology Z.smallEtaleTopology).obj G).1 ≃
        Scheme.Etale.stalk
          (@Scheme.GeometricPoint.of Z xbar.K inferInstance xbar.isAlgClosed s) G.1))
