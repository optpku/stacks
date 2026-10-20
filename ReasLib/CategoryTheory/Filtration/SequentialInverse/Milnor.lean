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

/-- The product comparison of a sequential inverse filtration is a monomorphism: the presented
object is the limit of its quotient tower. -/
instance mono_comparison {I : C} {admissibleEpi : MorphismProperty C}
    {pieceProperty : C → Prop} (F : SequentialInverseFiltration I admissibleEpi pieceProperty) :
    Mono (comparison F) := sorry

/-- The product short complex of a sequential inverse filtration is exact in the middle: the
presented object, being the limit of the tower, is the kernel of the Milnor difference map.  This
left-exact part holds for every tower; surjectivity of the difference map (vanishing of `lim¹`)
does not, see `shortExact_of_map_isSplitEpi`. -/
theorem exact {I : C} {admissibleEpi : MorphismProperty C}
    {pieceProperty : C → Prop} (F : SequentialInverseFiltration I admissibleEpi pieceProperty) :
    (shortComplex F).Exact := sorry

/-- The product short complex of a sequential inverse filtration is short exact as soon as some
faithful additive functor preserving the product of the quotient stages sends every successor
transition to a split epimorphism.  The Milnor difference map is then epic, since its image is
split epic by `SequentialInverseSystem.map_milnorDifferenceMap_isSplitEpi`.

Some splitting hypothesis is necessary: epic transitions alone (hence the Mittag-Leffler
condition) do not make the difference map epic in a general abelian category with countable
products, even one with exact products (Neeman's counterexample, cited in Stacks, Homology,
Definition `definition-Mittag-Leffler`). -/
theorem shortExact_of_map_isSplitEpi {D : Type*} [Category D] [Preadditive D]
    {I : C} {admissibleEpi : MorphismProperty C} {pieceProperty : C → Prop}
    (F : SequentialInverseFiltration I admissibleEpi pieceProperty) (G : C ⥤ D)
    [G.Additive] [G.Faithful] [PreservesLimit (Discrete.functor F.tower.family) G]
    (hsplit : ∀ n : ℕ, IsSplitEpi (G.map (F.tower.stepMap n))) :
    (shortComplex F).ShortExact := sorry

/-- The product short complex of a sequential inverse filtration whose successor transitions are
split epimorphisms is short exact. -/
theorem shortExact {I : C} {admissibleEpi : MorphismProperty C}
    {pieceProperty : C → Prop} (F : SequentialInverseFiltration I admissibleEpi pieceProperty)
    (hsplit : ∀ n : ℕ, IsSplitEpi (F.tower.stepMap n)) :
    (shortComplex F).ShortExact := sorry

end

end Milnor

end SequentialInverseFiltration

end CategoryTheory
