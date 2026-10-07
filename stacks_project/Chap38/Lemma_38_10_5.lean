module

import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.EtaleNeighborhood
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 38.10.5: a finite-type quasicoherent module that is flat at `x` over a
locally finite-type morphism becomes flat on an open neighborhood of the unique point
over `x`, after an elementary étale refinement followed by base change to the spectrum
of the selected stalk. -/
@[stacks 05KT]
#check
  (AlgebraicGeometry.Scheme.Modules.existsElementaryEtaleFlatNeighborhoodAt :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
      (x : X) (h_flat : flatOverAt F f x),
      ∃ U : EtaleNeighborhood.Elementary S (f x),
        let E := U.obj
        let g := Scheme.fromSpecStalk E.toEtale.left E.point ≫ E.toEtale.hom
        let X' := Limits.pullback f g
        let p := Limits.pullback.snd f g
        let F' := baseChangeModule f g F
        ∃ x' : X',
          (Limits.pullback.fst f g) ⁻¹' {x} = {x'} ∧
            ∃ V : X'.Opens, x' ∈ V ∧
              flatOver (F'.restrict V.ι) (V.ι ≫ p))

end AlgebraicGeometry.Scheme.Modules
