/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.EtaleNeighborhood
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 41.17.3: A finite unramified morphism becomes, after an étale base change,
a finite pairwise disjoint clopen decomposition whose pieces map to the neighbourhood by
closed immersions. -/
@[stacks 04HJ] #check
  (AlgebraicGeometry.Scheme.Hom.exists_clopen_decomposition_closedImmersion_of_finite :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Unramified f] (s : S),
      ∃ (U : EtaleNeighborhood S s) (n : ℕ),
        let P := pullback f U.toEtale.hom
        let p := pullback.snd f U.toEtale.hom
        ∃ (V : Fin n → P.Opens)
          (_ : iSup V = ⊤)
          (_ : Pairwise (fun i j ↦ Disjoint (V i : Set P) (V j : Set P)))
          (_ : ∀ i, IsClopen (V i : Set P)),
          ∀ i, IsClosedImmersion ((V i).ι ≫ p))

end AlgebraicGeometry.Scheme.Hom
