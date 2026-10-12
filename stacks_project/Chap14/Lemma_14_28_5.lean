/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.Cech.Conerve.SplitMono.Homotopy
import StacksCheckRecall

/-!
@stack 019Z
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X Y : C} {f : X ⟶ Y}
variable [HasPushouts C]
variable (r : SplitMono f)

/- Companion formula for Lemma 14.28.5 (019Z): on every coproduct factor, the retraction-induced
endomorphism is given by the idempotent `r.retraction ≫ f`. -/
@[stacks 019Z "factorwise formula"]
#check (SplitMono.cechConerve.retractionEndomorphism.map.app_ι r :
  ∀ (n : SimplexCategory) (i : Fin (n.len + 1)),
    Arrow.cechConerve.ι (Arrow.mk f) n i ≫
        (SplitMono.cechConerve.retractionEndomorphism.map r).app n =
      (r.retraction ≫ f) ≫ Arrow.cechConerve.ι (Arrow.mk f) n i)

/- Lemma 14.28.5 (019Z) (1): the endomorphism of the Čech conerve induced by the retraction of
a split monomorphism is product-free `Δ[1]`-homotopic to the identity. -/
@[stacks 019Z "homotopy"]
#check (SplitMono.cechConerve.retractionEndomorphism.homotopic_id r :
  CosimplicialObject.DeltaOneHomotopic
    (SplitMono.cechConerve.retractionEndomorphism.map r)
    (𝟙 ((Arrow.mk f).cechConerve)))

#check (SplitMono.cechConerve.retractionEndomorphism.homotopy r :
  CosimplicialObject.DeltaOneHomotopy
    (SplitMono.cechConerve.retractionEndomorphism.map r)
    (𝟙 ((Arrow.mk f).cechConerve)))

#check (fun {n : SimplexCategory} ↦
  SplitMono.cechConerve.retractionEndomorphism.homotopy.hom r (n := n))

/- Lemma 14.28.5 (019Z) (2): the Čech conerve of a split monomorphism is homotopy equivalent
to the constant cosimplicial object on its source. -/
@[stacks 019Z "homotopy equivalence"]
#check (SplitMono.cechConerve.coaugmentation.homotopyEquiv r :
  CosimplicialObject.HomotopyEquiv
    ((CosimplicialObject.const C).obj X) (Arrow.mk f).cechConerve)

#check SplitMono.cechConerve.coaugmentation.homotopyEquiv.hom r
#check SplitMono.cechConerve.coaugmentation.homotopyEquiv.inv r

/- The canonical relation-level API and its explicit `Δ[1]` presentation name. -/
#check HomRel.Equiv.toIso
#check CosimplicialObject.IsHomotopyEquivalence.iff_exists_equiv
#check CosimplicialObject.homotopyRel
#check CosimplicialObject.homotopyRel_iff

end CategoryTheory
