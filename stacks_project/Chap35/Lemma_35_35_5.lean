/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Pullback
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DescentData.Pullback

variable {X S : Scheme.{u}}

/- Lemma 35.35.5: pullback by an endomorphism of `X` over `S` is naturally isomorphic
to the identity functor on descent data relative to `a : X ⟶ S`. -/
@[stacks 0242] #check
  (AlgebraicGeometry.Scheme.DescentData.Pullback.selfIso :
    (a : X ⟶ S) → (f : X ⟶ X) → (sq : CommSq f a a (𝟙 S)) →
    functor a a (𝟙 S) f sq ≅
      𝟭 (DescentData (fun _ : PUnit.{1} ↦ X) (fun _ : PUnit.{1} ↦ a)))

#check
  (AlgebraicGeometry.Scheme.DescentData.Pullback.selfIso_hom_app :
    ∀ (a : X ⟶ S) (f : X ⟶ X) (sq : CommSq f a a (𝟙 S))
    (D : DescentData (fun _ : PUnit.{1} ↦ X) (fun _ : PUnit.{1} ↦ a)),
    (selfIso a f sq).hom.app D =
      (iso a a (𝟙 S) f (𝟙 X) sq CommSq.mk).hom.app D ≫
        (Pseudofunctor.DescentData.pullFunctorIdIso
          Scheme.overPseudofunctor S).hom.app D)

end AlgebraicGeometry.Scheme.DescentData.Pullback
