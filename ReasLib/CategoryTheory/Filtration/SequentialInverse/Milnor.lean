module

public import ReasLib.CategoryTheory.Filtration.SequentialInverse
public import ReasLib.CategoryTheory.InverseSystem.Milnor

@[expose] public section

/-!
# Milnor Product Sequences of Sequential Inverse Filtrations

This leaf adds the product-level Milnor sequence to the basic chosen-limit
presentation.  Keeping it separate lets clients which only manipulate a
tower, its cone, and its limit comparison avoid product assumptions.
-/

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

namespace SequentialInverseFiltration

namespace Milnor

section

variable [Preadditive C] [HasCountableProducts C]

/-- The canonical map from the categorical limit of a sequential inverse filtration to the
product of its quotient stages. -/
noncomputable abbrev limitToProduct {I : C} {admissibleEpi : MorphismProperty C}
    {pieceProperty : C → Prop}
    (F : SequentialInverseFiltration I admissibleEpi pieceProperty) :
    limit F.tower ⟶ ∏ᶜ F.tower.family :=
  Pi.lift fun n ↦ limit.π F.tower (op n)

/-- The quotient-stage component of the canonical map from a limit to the product of the stages.
-/
@[reassoc]
theorem limitToProduct_comp_π {I : C} {admissibleEpi : MorphismProperty C}
    {pieceProperty : C → Prop} (F : SequentialInverseFiltration I admissibleEpi pieceProperty)
    (n : ℕ) :
    limitToProduct F ≫ Pi.π F.tower.family n = limit.π F.tower (op n) := sorry

/-- The canonical map from the object presented by a sequential inverse filtration to the product
of its quotient stages. -/
noncomputable abbrev comparison {I : C} {admissibleEpi : MorphismProperty C}
    {pieceProperty : C → Prop} (F : SequentialInverseFiltration I admissibleEpi pieceProperty) :
    I ⟶ ∏ᶜ F.tower.family :=
  F.limitComparison.hom ≫ limitToProduct F

/-- The `n`th quotient-stage component of the product comparison is the supplied cone map. -/
@[reassoc]
theorem comparison_comp_π {I : C} {admissibleEpi : MorphismProperty C}
    {pieceProperty : C → Prop} (F : SequentialInverseFiltration I admissibleEpi pieceProperty)
    (n : ℕ) :
    comparison F ≫ Pi.π F.tower.family n = F.coneApp n := sorry

/-- The product comparison of a sequential inverse filtration is killed by the Milnor difference
map of its quotient tower. -/
theorem comparison_comp_difference_zero {I : C}
    {admissibleEpi : MorphismProperty C} {pieceProperty : C → Prop}
    (F : SequentialInverseFiltration I admissibleEpi pieceProperty) :
    comparison F ≫ F.tower.milnorDifferenceMap = 0 := sorry

/-- The product short complex associated to a sequential inverse filtration. -/
noncomputable abbrev shortComplex {I : C} {admissibleEpi : MorphismProperty C}
    {pieceProperty : C → Prop} (F : SequentialInverseFiltration I admissibleEpi pieceProperty) :
    ShortComplex C :=
  ShortComplex.mk (comparison F) F.tower.milnorDifferenceMap
    (comparison_comp_difference_zero F)

end

section

variable [Abelian C] [HasCountableProducts C]

/-- The product short complex of a sequential inverse filtration is short exact. -/
theorem shortExact {I : C} {admissibleEpi : MorphismProperty C}
    {pieceProperty : C → Prop} (F : SequentialInverseFiltration I admissibleEpi pieceProperty) :
    (shortComplex F).ShortExact := sorry

end

end Milnor

end SequentialInverseFiltration

end CategoryTheory
