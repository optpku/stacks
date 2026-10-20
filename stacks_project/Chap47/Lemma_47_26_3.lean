module

public import ReasLib.Algebra.Module.Injective.FlatLocal
import StacksCheckRecall

@[expose] public section

open IsLocalRing
open scoped TensorProduct TensorProduct.Right

universe u v w

/- Lemma 47.26.3: Let `A → B` be a flat local homomorphism of Noetherian local rings
such that the maximal ideal of `B` is extended from `A`. Scalar extension to `B` of an
injective hull of `ResidueField A` is an injective hull of `ResidueField B`. -/
@[stacks 0E4E] #check
  (LinearMap.IsInjectiveHull.baseChange_of_flat_of_mapsMaximalIdeal :
    ∀ {A : Type u} {B : Type v} {E : Type w}
      [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
      [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
      [AddCommGroup E] [Module A E] [Module.Injective A E]
      (hmax : (algebraMap A B).MapsMaximalIdeal)
      (iota : ResidueField A →ₗ[A] E) (hiota : iota.IsInjectiveHull),
      @LinearMap.IsInjectiveHull B _ (ResidueField B) _ _ (E ⊗[A] B) _ _
        (LinearMap.IsInjectiveHull.injective_tensorProduct_of_flat_of_mapsMaximalIdeal
          hmax iota hiota)
        (LinearMap.IsInjectiveHull.baseChangeResidueMap hmax iota))
