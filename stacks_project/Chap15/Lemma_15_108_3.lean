/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Etale.Neighborhood.GeometricallyUnibranch.Local

/-!
@stack 0GS6
-/

@[expose] public section

open IsLocalRing

universe u v

/- Lemma 15.108.3: let `(A, maximalIdeal A)` be a geometrically unibranch
local domain and let `A → B` be an injective local homomorphism of local rings
that is essentially of finite type.  If the source maximal ideal extends to
`maximalIdeal B` and the residue-field extension is separable, then `B` is a
localization of an etale `A`-algebra.  The historical snapshot maps to current
Stacks 15.109.3, tag `0GS6`. -/
@[stacks 0GS6 "Lemma 15.108.3"]
#check fun (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsGeometricallyUnibranch A]
    [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra.EssFiniteType A B]
    (h_injective : Function.Injective (algebraMap A B))
    (h_maximal : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B)
    (h_separable : Algebra.IsSeparable (ResidueField A) (ResidueField B)) ↦
  ((Algebra.essEtale_iff_exists_etale A B).mp
      (Algebra.EssEtale.of_geometricallyUnibranch_of_injective
        (A := A) (B := B) h_injective h_maximal h_separable) :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
      (_ : IsScalarTower A C B) (M : Submonoid C),
        Algebra.Etale A C ∧ IsLocalization M B)

end
