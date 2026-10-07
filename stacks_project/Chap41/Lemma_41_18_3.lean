module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Finite
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 41.18.3: A finite étale morphism becomes, after an étale base change, a finite
pairwise disjoint clopen decomposition whose pieces map isomorphically to the neighbourhood. -/
@[stacks 04HN] #check
  (AlgebraicGeometry.Scheme.Hom.exists_clopen_decomposition_isIso_of_finite :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Etale f] (s : S),
      ∃ (U : EtaleNeighborhood S s) (n : ℕ),
        let P := pullback f U.toEtale.hom
        let p := pullback.snd f U.toEtale.hom
        ∃ (V : Fin n → P.Opens)
          (_ : iSup V = ⊤)
          (_ : Pairwise (fun i j ↦ Disjoint (V i : Set P) (V j : Set P)))
          (_ : ∀ i, IsClopen (V i : Set P)),
          ∀ i, IsIso ((V i).ι ≫ p))

end AlgebraicGeometry.Scheme.Hom
