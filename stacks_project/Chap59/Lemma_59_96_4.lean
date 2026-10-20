module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Proper
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

/- Lemma 59.96.4: if `f : X ⟶ Y` is a proper morphism of schemes and `n ≥ 1`,
then `Rf_* : D(X_étale, ZMod n) ⟶ D(Y_étale, ZMod n)` preserves direct sums. -/
@[stacks 0F0D] #check (AlgebraicGeometry.Scheme.etalePushforwardDerived_preservesCoproducts_of_isProper :
  ∀ {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] (n : ℕ) (hn : 0 < n)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} (ZMod n)) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} (ZMod n)) Y.smallEtaleTopology X.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))) (ComplexShape.up ℤ))]
    (I : Type u)
    [HasColimitsOfShape (Discrete I)
      (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))))]
    [HasColimitsOfShape (Discrete I)
      (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))))],
    PreservesColimitsOfShape (Discrete I)
      (RightDerived.Cochain.functor
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} (ZMod n)) Y.smallEtaleTopology X.smallEtaleTopology)))

end
