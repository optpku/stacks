module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.FiniteLocallyFreeCover
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.CommSq

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.EtaleNeighborhood

/-- An étale neighbourhood of a pointed scheme is locally dominated over an affine open
neighbourhood by a surjective finite locally free morphism, with pointed local factorizations
through the original étale neighbourhood. -/
theorem exists_finiteLocallyFreeCover {S : Scheme.{u}} {s : S}
    (U : EtaleNeighborhood S s) :
    ∃ (V : S.affineOpens) (hs : s ∈ (V : S.Opens)) (T : Scheme.{u})
      (π : T ⟶ (V : S.Opens).toScheme) (_ : Surjective π) (_ : IsFiniteLocallyFree π),
      ∀ (t : T) (ht : π t = ⟨s, hs⟩),
        ∃ (W : T.Opens) (htW : t ∈ W) (h : W.toScheme ⟶ U.toEtale.left),
          CommSq h (W.ι ≫ π) U.toEtale.hom (V : S.Opens).ι ∧
            h ⟨t, htW⟩ = U.point := sorry

end AlgebraicGeometry.Scheme.EtaleNeighborhood
