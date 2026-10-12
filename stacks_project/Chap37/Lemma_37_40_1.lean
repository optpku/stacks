/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.FiniteLocallyFreeCover
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.EtaleNeighborhood

/- Lemma 37.40.1: an étale neighbourhood of a pointed scheme is locally dominated
by a surjective finite locally free morphism over an affine open neighbourhood, with
pointed local factorizations through the original étale neighbourhood. -/
@[stacks 02LG] #check
  (AlgebraicGeometry.Scheme.EtaleNeighborhood.exists_finiteLocallyFreeCover :
    ∀ {S : Scheme.{u}} {s : S} (U : EtaleNeighborhood S s),
      ∃ (V : S.affineOpens) (hs : s ∈ (V : S.Opens)) (T : Scheme.{u})
        (π : T ⟶ (V : S.Opens).toScheme) (_ : Surjective π) (_ : IsFiniteLocallyFree π),
        ∀ (t : T) (ht : π t = ⟨s, hs⟩),
          ∃ (W : T.Opens) (htW : t ∈ W) (h : W.toScheme ⟶ U.toEtale.left),
            CommSq h (W.ι ≫ π) U.toEtale.hom (V : S.Opens).ι ∧
              h ⟨t, htW⟩ = U.point)

end AlgebraicGeometry.Scheme.EtaleNeighborhood
