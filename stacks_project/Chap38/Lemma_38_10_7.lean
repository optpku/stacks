module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.EtaleNeighborhood
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 38.10.7: if a finite-type quasicoherent module is fibrewise flat over a
finite-type morphism, then after one elementary étale refinement it is relatively flat
on an open containing the entire closed fibre. -/
@[stacks 05KV] #check
  (AlgebraicGeometry.Scheme.Modules.existsElementaryEtaleFlatNeighborhood_of_finiteType :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FiniteType f]
      (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
      (s : S), (∀ x : f.fiber s, flatOverAt F f (f.fiberι s x)) →
        ∃ U : EtaleNeighborhood.Elementary S s,
          let E := U.obj
          let T := E.toEtale.left
          let g := T.fromSpecStalk E.point ≫ E.toEtale.hom
          let X' := Limits.pullback f g
          let p := Limits.pullback.snd f g
          let F' := baseChangeModule f g F
          let s' := IsLocalRing.closedPoint (T.presheaf.stalk E.point)
          ∃ V : X'.Opens, Set.range (p.fiberι s') ⊆ (V : Set X') ∧
            flatOver (F'.restrict V.ι) (V.ι ≫ p))

end AlgebraicGeometry.Scheme.Modules
