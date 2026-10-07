module

public import stacks_project.Chap42.Lemma_42_61_2_Comparison
public import stacks_project.Chap42.Remark_42_33_6_Commutation
public import stacks_project.Chap42.Remark_42_34_2_Restriction
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- Lemma 42.61.3: after base change to `X ⨯ Z`, every bivariant class on
`X ⟶ Spec k` commutes with every bivariant class on `Y ⟶ Z`; the canonical
common pullback is identified with `X ⨯ Y`. -/
@[stacks 0FBX]
theorem commuteOfField
    {k : Type u} [Field k] {X Y Z : SchemeOverField k}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom]
    (g : Y ⟶ Z) (p q : ℤ)
    (c : BivariantClass (fun _ ↦ 0) (terminal.from X) p)
    (c' : BivariantClass (fun _ ↦ 0) g q) :
    Commute (fun _ ↦ 0) (Limits.prod.snd : X ⨯ Z ⟶ Z) g
      (restrict (fun _ ↦ 0) (Limits.prod.fst : X ⨯ Z ⟶ X)
        (Limits.prod.snd : X ⨯ Z ⟶ Z) (terminal.from Z)
        (SchemeOverField.productIsPullback X (terminal.from Z)) p c) c' := sorry

end AlgebraicGeometry.BivariantClass
