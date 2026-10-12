/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.OverField.Commutation
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/- Lemma 42.61.3: after base change to `X ⨯ Z`, every bivariant class on
`X ⟶ Spec k` commutes with every bivariant class on `Y ⟶ Z`; the canonical
common pullback is identified with `X ⨯ Y`. -/
@[stacks 0FBX] #check (AlgebraicGeometry.BivariantClass.commuteOfField :
  {k : Type u} → [Field k] → {X Y Z : SchemeOverField k} →
    [LocallyOfFiniteType X.hom] → [LocallyOfFiniteType Y.hom] →
    [LocallyOfFiniteType Z.hom] →
    (g : Y ⟶ Z) → (p q : ℤ) →
    (c : BivariantClass (fun _ ↦ 0) (terminal.from X) p) →
    (c' : BivariantClass (fun _ ↦ 0) g q) →
    AlgebraicGeometry.BivariantClass.Commute
      (fun _ ↦ 0) (Limits.prod.snd : X ⨯ Z ⟶ Z) g
      (AlgebraicGeometry.BivariantClass.restrict
        (fun _ ↦ 0) (Limits.prod.fst : X ⨯ Z ⟶ X)
        (Limits.prod.snd : X ⨯ Z ⟶ Z) (terminal.from Z)
        (SchemeOverField.productIsPullback X (terminal.from Z)) p c) c')
