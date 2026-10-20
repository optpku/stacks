/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.WContractible.Cover
public import ReasLib.Algebra.WLocalIndEtale.Cardinality
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Cardinality bounds for w-contractible extensions

Every commutative ring admits a faithfully flat ind-étale w-contractible
extension with a cardinality bound in terms of any infinite cardinal bounding
the original ring.
-/

@[expose] public section

universe u v

open scoped Cardinal

namespace IsWContractibleRing

/-- For every commutative ring `A` and every infinite cardinal `κ` bounding its
cardinality, there exists a faithfully flat ind-étale ring map to a
w-contractible ring of cardinality at most
`κ ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ)))`. -/
theorem exists_faithfullyFlat_indEtale_cardinalMk_le
    (A : Type u) [CommRing A] {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hA : #A ≤ κ) :
    ∃ (D : Type u) (_ : CommRing D) (f : A →+* D),
      f.FaithfullyFlat ∧ f.IndEtale ∧ IsWContractibleRing.{u, v} D ∧
        #D ≤ κ ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ))) :=
  sorry

/-- There exists a faithfully flat ind-étale `A`-algebra whose underlying ring
is w-contractible of cardinality at most
`κ ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ)))`. -/
theorem exists_faithfullyFlat_indEtale_algebra_cardinalMk_le
    (A : Type u) [CommRing A] {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hA : #A ≤ κ) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra A D),
      Module.FaithfullyFlat A D ∧ (algebraMap A D).IndEtale ∧
        IsWContractibleRing.{u, v} D ∧
          #D ≤ κ ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ))) :=
  sorry

/-- Every commutative ring admits a faithfully flat ind-étale w-contractible
extension of cardinality at most
`(#A ⊔ ℵ₀) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ (#A ⊔ ℵ₀))))`. -/
theorem exists_faithfullyFlat_indEtale_cardinalMk_le_max (A : Type u) [CommRing A] :
    ∃ (D : Type u) (_ : CommRing D) (f : A →+* D),
      f.FaithfullyFlat ∧ f.IndEtale ∧ IsWContractibleRing.{u, v} D ∧
        #D ≤ (#A ⊔ ℵ₀) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ (#A ⊔ ℵ₀)))) :=
  sorry

end IsWContractibleRing
