module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.CompleteDevissage.EtaleCover

open AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 38.5.8: after an elementary étale pointed base change, a finite-type
quasicoherent module admits complete dévissages on a finite étale family covering the
distinguished fibre. -/
@[stacks 05HU] #check
  (AlgebraicGeometry.Scheme.Modules.existsEtaleCoverWithCompleteDevissages :
    {X S : Scheme.{u}} → (f : X ⟶ S) → [Scheme.Hom.FiniteType f] →
      (F : X.Modules) → [F.IsQuasicoherent] → [F.IsFiniteType] → (s : S) →
        ∃ U : Scheme.EtaleNeighborhood.Elementary S s,
          let E := U.obj
          let g := E.toEtale.hom
          let X' := Limits.pullback f g
          let p := Limits.pullback.snd f g
          ∃ n : ℕ, ∃ Y : Fin n → X'.Etale,
            ∃ D : ∀ i, Scheme.Modules.CompleteDevissageOver (((Y i).left ↘ X') ≫ p)
              ((Scheme.Modules.pullback
                (((Y i).left ↘ X') ≫ Limits.pullback.fst f g)).obj F) E.point,
              Set.range (p.fiberι E.point) ⊆ ⋃ i, Set.range (Y i).hom)
