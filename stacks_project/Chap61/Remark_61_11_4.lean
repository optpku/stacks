module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import ReasLib.RingTheory.RingHom.IndEtale.Basic
public import stacks_project.Chap61.Definition_61_11_1_WContractible
public import stacks_project.Chap61.Remark_61_11_4_Cardinality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Remark 61.11.4

A cardinality bound on a faithfully flat ind-étale w-contractible extension.
-/

@[expose] public section

universe u

open scoped Cardinal

namespace IsWContractibleRing

/-- Remark 61.11.4: if `A` is a commutative ring and `κ` is an infinite cardinal
with `#A ≤ κ`, then there exists a faithfully flat, ind-étale ring map
`f : A →+* D` such that `D` is w-contractible and
`#D ≤ κ ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ)))`. -/
@[stacks 0984]
theorem exists_faithfullyFlat_indEtale_cardinalMk_le
    (A : Type u) [CommRing A] {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hA : #A ≤ κ) :
    ∃ (D : Type u) (_ : CommRing D) (f : A →+* D),
      f.FaithfullyFlat ∧ f.IndEtale ∧ IsWContractibleRing D ∧
        #D ≤ κ ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ))) :=
  sorry

/-- There exists a faithfully flat ind-étale `A`-algebra whose underlying ring
is w-contractible of cardinality at most
`κ ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ)))`. -/
theorem exists_faithfullyFlat_indEtale_algebra_cardinalMk_le
    (A : Type u) [CommRing A] {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hA : #A ≤ κ) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra A D),
      Module.FaithfullyFlat A D ∧ (algebraMap A D).IndEtale ∧
        IsWContractibleRing D ∧
          #D ≤ κ ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ))) :=
  sorry

/-- Equivalent packaging: there exists a faithfully flat, ind-étale,
w-contractible extension of `A` of cardinality at most
`(#A ⊔ ℵ₀) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ (#A ⊔ ℵ₀))))`. -/
theorem exists_faithfullyFlat_indEtale_cardinalMk_le_max (A : Type u) [CommRing A] :
    ∃ (D : Type u) (_ : CommRing D) (f : A →+* D),
      f.FaithfullyFlat ∧ f.IndEtale ∧ IsWContractibleRing D ∧
        #D ≤ (#A ⊔ ℵ₀) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ (#A ⊔ ℵ₀)))) :=
  sorry

end IsWContractibleRing
