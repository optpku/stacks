/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Abelian.Projective.Ext
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Abelian.Ext CategoryTheory.Limits

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (P : C)

/- Lemma 12.28.2 (1) ↔ (2) [013C]: projectivity is detected by exactness of the preadditive
co-Yoneda functor. -/
@[stacks 013C]
#check (projective_iff_exact_preadditiveCoyonedaObj P :
  Projective P ↔ exactFunctor _ _ (preadditiveCoyonedaObj P))

/- Lemma 12.28.2 (1) ↔ (3) [013C]: projectivity is detected by splitting every short exact
sequence ending at the object. -/
@[stacks 013C]
#check (projective_iff_shortExact_isSplitEpi P :
  Projective P ↔
    ∀ ⦃S : ShortComplex C⦄, S.X₃ = P → S.ShortExact → IsSplitEpi S.g)

section

variable [HasExt.{w} C]

/- Lemma 12.28.2 (1) ↔ (4) [013C]: projectivity is detected by vanishing of all degree-one
extensions out of the object. -/
@[stacks 013C]
#check (projective_iff_ext_one_eq_zero P :
  Projective P ↔ ∀ ⦃A : C⦄ (e : Ext P A 1), e = 0)

/- Lemma 12.28.2 [013C]: the source's four equivalent characterizations. -/
@[stacks 013C]
#check (projective_tfae P :
  List.TFAE [
    Projective P,
    exactFunctor _ _ (preadditiveCoyonedaObj P),
    ∀ ⦃S : ShortComplex C⦄, S.X₃ = P → S.ShortExact → IsSplitEpi S.g,
    ∀ ⦃A : C⦄ (e : Ext P A 1), e = 0])

end
