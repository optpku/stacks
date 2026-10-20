module

public import ReasLib.CategoryTheory.Limits.Fubini.Colimits.Comparison
public import ReasLib.CategoryTheory.Limits.Fubini.Limits.Comparison
import StacksCheckRecall

@[expose] public section

universe vI uI vJ uJ vC uC

namespace CategoryTheory.Limits

variable {I : Type uI} [Category.{vI} I]
variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]

section ColimitExistence

variable (M : I × J ⥤ C)
variable (D : DiagramOfCocones (Functor.curry.obj M))
variable (hD : ∀ i, IsColimit (D.obj i))

/- Lemma 4.14.10 (1): rowwise colimit functor and total colimit exist together. -/
@[stacks 002M "rowwise colimit functor and total colimit exist together"]
#check (DiagramOfCocones.hasColimit_iff (M := M) D hD :
  HasColimit D.coconePoints ↔ HasColimit M)

end ColimitExistence

section ColimitIso

variable (M : I × J ⥤ C)
variable (D : DiagramOfCocones (Functor.curry.obj M))
variable (hD : ∀ i, IsColimit (D.obj i))
variable [HasColimit D.coconePoints] [HasColimit M]

/- Lemma 4.14.10 (2): canonical identification of iterated and total colimit. -/
@[stacks 002M "canonical identification of iterated and total colimit"]
#check (DiagramOfCocones.colimitIso (M := M) D hD :
  colimit D.coconePoints ≅ colimit M)

end ColimitIso

section ColimitSwap

variable (M : I × J ⥤ C)
variable (D : DiagramOfCocones (Functor.curry.obj M))
variable (hD : ∀ i, IsColimit (D.obj i))
variable (E : DiagramOfCocones (Functor.curry.obj (Prod.swap J I ⋙ M)))
variable (hE : ∀ j, IsColimit (E.obj j))
variable [HasColimit D.coconePoints] [HasColimit E.coconePoints] [HasColimit M]

/- Lemma 4.14.10 (3): canonical identification of the two iterated colimit orders. -/
@[stacks 002M "canonical identification of the two iterated colimit orders"]
#check (DiagramOfCocones.swapIso (M := M) D hD E hE :
  colimit D.coconePoints ≅ colimit E.coconePoints)

end ColimitSwap

section LimitExistence

variable (M : I × J ⥤ C)
variable (D : DiagramOfCones (Functor.curry.obj M))
variable (hD : ∀ i, IsLimit (D.obj i))

/- Lemma 4.14.10 (4): rowwise limit functor and total limit exist together. -/
@[stacks 002M "rowwise limit functor and total limit exist together"]
#check (DiagramOfCones.hasLimit_iff (M := M) D hD :
  HasLimit D.conePoints ↔ HasLimit M)

end LimitExistence

section LimitIso

variable (M : I × J ⥤ C)
variable (D : DiagramOfCones (Functor.curry.obj M))
variable (hD : ∀ i, IsLimit (D.obj i))
variable [HasLimit D.conePoints] [HasLimit M]

/- Lemma 4.14.10 (5): canonical identification of iterated and total limit. -/
@[stacks 002M "canonical identification of iterated and total limit"]
#check (DiagramOfCones.limitIso (M := M) D hD :
  limit D.conePoints ≅ limit M)

end LimitIso

section LimitSwap

variable (M : I × J ⥤ C)
variable (D : DiagramOfCones (Functor.curry.obj M))
variable (hD : ∀ i, IsLimit (D.obj i))
variable (E : DiagramOfCones (Functor.curry.obj (Prod.swap J I ⋙ M)))
variable (hE : ∀ j, IsLimit (E.obj j))
variable [HasLimit D.conePoints] [HasLimit E.conePoints] [HasLimit M]

/- Lemma 4.14.10 (6): canonical identification of the two iterated limit orders. -/
@[stacks 002M "canonical identification of the two iterated limit orders"]
#check (DiagramOfCones.swapIso (M := M) D hD E hE :
  limit D.conePoints ≅ limit E.conePoints)

end LimitSwap

end CategoryTheory.Limits
