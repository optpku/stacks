module

public import ReasLib.RingTheory.Etale.WContractible.Cardinality
import StacksCheckRecall

/-!
# Remark 61.11.4

A cardinality bound on a faithfully flat ind-étale w-contractible extension.
-/

@[expose] public section

universe u v

open scoped Cardinal

/- Remark 61.11.4: if `A` is a commutative ring and `κ` is an infinite cardinal
with `#A ≤ κ`, then there exists a faithfully flat, ind-étale ring map
`f : A →+* D` such that `D` is w-contractible and
`#D ≤ κ ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ)))`. -/
@[stacks 0984] #check (IsWContractibleRing.exists_faithfullyFlat_indEtale_cardinalMk_le :
  ∀ (A : Type u) [CommRing A] {κ : Cardinal.{u}}, ℵ₀ ≤ κ → #A ≤ κ →
    ∃ (D : Type u) (_ : CommRing D) (f : A →+* D),
      f.FaithfullyFlat ∧ f.IndEtale ∧ IsWContractibleRing.{u, v} D ∧
        #D ≤ κ ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ))))

/- There exists a faithfully flat ind-étale `A`-algebra whose underlying ring
is w-contractible of cardinality at most
`κ ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ)))`. -/
#check (IsWContractibleRing.exists_faithfullyFlat_indEtale_algebra_cardinalMk_le :
  ∀ (A : Type u) [CommRing A] {κ : Cardinal.{u}}, ℵ₀ ≤ κ → #A ≤ κ →
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra A D),
      Module.FaithfullyFlat A D ∧ (algebraMap A D).IndEtale ∧
        IsWContractibleRing.{u, v} D ∧
          #D ≤ κ ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ))))

/- Equivalent packaging: there exists a faithfully flat, ind-étale,
w-contractible extension of `A` of cardinality at most
`(#A ⊔ ℵ₀) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ (#A ⊔ ℵ₀))))`. -/
#check (IsWContractibleRing.exists_faithfullyFlat_indEtale_cardinalMk_le_max :
  ∀ (A : Type u) [CommRing A],
    ∃ (D : Type u) (_ : CommRing D) (f : A →+* D),
      f.FaithfullyFlat ∧ f.IndEtale ∧ IsWContractibleRing.{u, v} D ∧
        #D ≤ (#A ⊔ ℵ₀) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ (#A ⊔ ℵ₀)))))
