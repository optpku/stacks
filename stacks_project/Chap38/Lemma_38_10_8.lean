module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.EtaleNeighborhood

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 38.10.8: a locally finite-type morphism that is flat at `x` becomes flat and
of finite presentation on an open neighborhood of the unique point above `x`, after an
elementary étale refinement and base change to the spectrum of the selected stalk. -/
@[stacks 05I6] #check
  (AlgebraicGeometry.Scheme.Hom.exists_elementaryEtale_flat_finitePresentation :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (x : X) (_ : f.flatAt x),
      ∃ U : EtaleNeighborhood.Elementary S (f x),
        let E := U.obj
        let g := Scheme.fromSpecStalk E.toEtale.left E.point ≫ E.toEtale.hom
        let X' := Limits.pullback f g
        let p := Limits.pullback.snd f g
        ∃ x' : X',
          (Limits.pullback.fst f g) ⁻¹' {x} = {x'} ∧
            ∃ V : X'.Opens, x' ∈ V ∧
              Flat (V.ι ≫ p) ∧ Scheme.Hom.FinitePresentation (V.ι ≫ p))

end AlgebraicGeometry.Scheme.Hom
