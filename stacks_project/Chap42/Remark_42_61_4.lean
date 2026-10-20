module

public import ReasLib.AlgebraicGeometry.ChowGroup.ExteriorProduct.Cap
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/- Remark 42.61.4: over a field, exterior product by a Chow class commutes with
the cap action of a bivariant class after base change along the product map. -/
@[stacks 0FBY] #check (AlgebraicGeometry.ChowGroup.exteriorProduct_cap :
  {k : Type u} → [Field k] → {X Y Z : SchemeOverField k} →
    [LocallyOfFiniteType X.hom] → [LocallyOfFiniteType Y.hom] →
    [LocallyOfFiniteType Z.hom] →
    (g : Y ⟶ Z) → (n m q : ℤ) →
    (α : RelativeChow (fun _ ↦ 0) X n) →
    (c' : BivariantClass (fun _ ↦ 0) g q) →
    (β : RelativeChow (fun _ ↦ 0) Z m) →
      RelativeChow.castDegree (fun _ ↦ 0) (Int.add_sub_assoc n m q).symm
          (AlgebraicGeometry.ChowGroup.exteriorProductPairing X Y n (m - q) α
            (c'.cap (𝟙 Y) g (𝟙 Z) IsPullback.of_id_fst m β)) =
        c'.cap (Limits.prod.snd : X ⨯ Y ⟶ Y)
          (Limits.prod.map (𝟙 X) g : X ⨯ Y ⟶ X ⨯ Z)
          (Limits.prod.snd : X ⨯ Z ⟶ Z)
          (AlgebraicGeometry.SchemeOverField.prodMapSndIsPullback X g) (n + m)
          (AlgebraicGeometry.ChowGroup.exteriorProductPairing X Z n m α β))
