module

public import ReasLib.AlgebraicGeometry.Scheme.AffineOpen.DimensionOne
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 33.42.4: an integral separated scheme admits an affine open containing any finite set
of points whose stalks are Noetherian of Krull dimension at most one. -/
@[stacks 09NJ] #check
  (AlgebraicGeometry.Scheme.exists_affineOpen_containing_finiteSet_of_stalkNoetherianDimLEOne :
    ∀ {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated]
      (S : Set X) (hS : S.Finite)
      (hNoeth : ∀ x : X, x ∈ S → IsNoetherianRing (X.presheaf.stalk x))
      (hDim : ∀ x : X, x ∈ S → ringKrullDim (X.presheaf.stalk x) ≤ 1),
      ∃ U : X.affineOpens, S ⊆ ((U : X.Opens) : Set X))
