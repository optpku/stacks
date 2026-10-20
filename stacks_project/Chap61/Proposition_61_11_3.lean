module

public import ReasLib.RingTheory.Etale.WContractible.Cover
import StacksCheckRecall

/-!
# Proposition 61.11.3

Every commutative ring admits a faithfully flat ind-étale extension whose
target is w-contractible.
-/

@[expose] public section

universe u v

/- Proposition 61.11.3: for every commutative ring `A` there exists a
faithfully flat, ind-étale ring map `f : A →+* D` such that `D` is
w-contractible. -/
@[stacks 0983] #check (IsWContractibleRing.exists_faithfullyFlat_indEtale :
  ∀ (A : Type u) [CommRing A],
    ∃ (D : Type u) (_ : CommRing D) (f : A →+* D),
      f.FaithfullyFlat ∧ f.IndEtale ∧ IsWContractibleRing.{u, v} D)

/- There exists a faithfully flat ind-étale `A`-algebra whose underlying ring
is w-contractible. -/
#check (IsWContractibleRing.exists_faithfullyFlat_indEtale_algebra :
  ∀ (A : Type u) [CommRing A],
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra A D),
      Module.FaithfullyFlat A D ∧ (algebraMap A D).IndEtale ∧
        IsWContractibleRing.{u, v} D)
