module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Module.CompleteDevissage.BaseChange

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- After an elementary étale pointed base change, a finite-type quasicoherent module admits
complete dévissages on a finite family of étale schemes covering the distinguished fibre. -/
theorem existsEtaleCoverWithCompleteDevissages {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.FiniteType f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (s : S) :
    ∃ U : Scheme.EtaleNeighborhood.Elementary S s,
      let E := U.obj
      let g := E.toEtale.hom
      let X' := Limits.pullback f g
      let p := Limits.pullback.snd f g
      ∃ n : ℕ, ∃ Y : Fin n → X'.Etale,
        ∃ D : ∀ i, CompleteDevissageOver (((Y i).left ↘ X') ≫ p)
          ((Scheme.Modules.pullback
            (((Y i).left ↘ X') ≫ Limits.pullback.fst f g)).obj F) E.point,
          Set.range (p.fiberι E.point) ⊆ ⋃ i, Set.range (Y i).hom := sorry

end AlgebraicGeometry.Scheme.Modules
