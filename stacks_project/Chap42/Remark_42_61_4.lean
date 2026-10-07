module

public import stacks_project.Chap42.Lemma_42_61_3
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

namespace SchemeOverField

/-- The square formed by a product map and the second projections is cartesian. -/
theorem prodMapSndIsPullback (X : SchemeOverField k) {Y Z : SchemeOverField k}
    (g : Y ⟶ Z) :
    IsPullback (Limits.prod.snd : X ⨯ Y ⟶ Y).left
      (Limits.prod.map (𝟙 X) g : X ⨯ Y ⟶ X ⨯ Z).left g.left
      (Limits.prod.snd : X ⨯ Z ⟶ Z).left := sorry

end SchemeOverField

namespace ChowGroup

/-- Remark 42.61.4: over a field, exterior product by a Chow class commutes with
the cap action of a bivariant class. -/
@[stacks 0FBY]
theorem exteriorProduct_cap
    {X Y Z : SchemeOverField k}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom]
    (g : Y ⟶ Z) (n m q : ℤ)
    (α : RelativeChow (fun _ ↦ 0) X n)
    (c' : BivariantClass (fun _ ↦ 0) g q)
    (β : RelativeChow (fun _ ↦ 0) Z m) :
    BivariantClass.castRelativeDegree (fun _ ↦ 0) (Int.add_sub_assoc n m q).symm
        (exteriorProductPairing X Y n (m - q) α
          (c'.cap (𝟙 Y) g (𝟙 Z) IsPullback.of_id_fst m β)) =
      c'.cap (Limits.prod.snd : X ⨯ Y ⟶ Y)
        (Limits.prod.map (𝟙 X) g : X ⨯ Y ⟶ X ⨯ Z)
        (Limits.prod.snd : X ⨯ Z ⟶ Z)
        (SchemeOverField.prodMapSndIsPullback X g) (n + m)
        (exteriorProductPairing X Z n m α β) := sorry

end ChowGroup

end AlgebraicGeometry
