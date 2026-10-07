module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Fiber
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 35.33.5: in a commutative square of schemes with étale vertical arrows, the
induced morphism from the fibre over `v'` to the fibre over its image `v` is étale. -/
@[stacks 04NI] #check
  (AlgebraicGeometry.Etale.fiberMap_of_commSq :
    ∀ {U' V' U V : Scheme.{u}}
      (f' : U' ⟶ V') (i : U' ⟶ U) (g : V' ⟶ V) (f : U ⟶ V)
      [Etale i] [Etale g] (sq : CommSq i f' f g) (v' : V') (v : V)
      (hv : g v' = v),
      Etale (hv ▸ Scheme.Hom.fiberMap f' i g f sq v'))

end AlgebraicGeometry
