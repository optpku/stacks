module

public import ReasLib.AlgebraicGeometry.Scheme.SerreCondition.Reduced
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 28.12.4: a locally Noetherian scheme is reduced if and only if all of its stalks
satisfy Serre's conditions `(S₁)` and `(R₀)`. -/
@[stacks 0344] #check
  (AlgebraicGeometry.Scheme.isReduced_iff_stalkwise_serre :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X],
      AlgebraicGeometry.IsReduced X ↔
        (∀ x : X, SerreConditionS (X.presheaf.stalk x) 1) ∧
          ∀ x : X, SerreConditionR (X.presheaf.stalk x) 0)

#check (IsReduced.iff_serre :
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R],
    IsReduced R ↔ SerreConditionR R 0 ∧ SerreConditionS R 1)
