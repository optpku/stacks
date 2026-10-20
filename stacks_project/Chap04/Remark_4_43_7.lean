module

public import ReasLib.CategoryTheory.Monoidal.Duality.Comparison
import StacksCheckRecall

@[expose] public section

universe u v

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable (X Y Y' : C) [ExactPairing X Y]
variable (p : ExactPairing X Y) (p' : ExactPairing X Y')
variable (adj : tensorRight X ⊣ tensorRight Y)

/- Remark 4.43.7 (1): an exact pairing gives the corresponding tensor-right adjunction. -/
@[stacks 0FFR "right-tensor adjunction induced by a left dual"]
#check (tensorRightAdjunction X Y : tensorRight X ⊣ tensorRight Y)

/- Remark 4.43.7 (2): a right dual is unique up to a unique pairing-preserving isomorphism. -/
@[stacks 0FFR "unique structure-preserving isomorphism between left duals"]
#check (ExactPairing.rightDualIso.isUnique p p' :
  ExactPairing.RightDualIso p p' (rightDualIso p p') ∧
    ∀ i : Y ≅ Y', ExactPairing.RightDualIso p p' i →
      i = rightDualIso p p')

/- Remark 4.43.7 (3): compatibility means that the adjunction Hom-equivalence commutes with
left tensoring. -/
@[stacks 0FFR "compatibility of the adjunction with left tensoring"]
#check (Adjunction.CompatibleWithLeftTensoring adj : Prop)

/- Remark 4.43.7 (4): an exact pairing exists exactly when a compatible tensor-right adjunction
exists. -/
@[stacks 0FFR "left duals as tensor-compatible right adjoints"]
#check (ExactPairing.nonempty_iff_exists_compatibleAdjunction X Y :
  Nonempty (ExactPairing X Y) ↔
    ∃ adj' : tensorRight X ⊣ tensorRight Y,
      adj'.CompatibleWithLeftTensoring)

end CategoryTheory
