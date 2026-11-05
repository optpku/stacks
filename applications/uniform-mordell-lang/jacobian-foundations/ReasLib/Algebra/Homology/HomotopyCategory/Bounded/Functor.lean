module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Functor
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Map.Computation
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Map.Naturality
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Quotient

@[expose] public section

/-!
# Functoriality of bounded homotopy categories

This file compares termwise mapping before passage to the homotopy category with mapping after
passage to the homotopy category. Pointwise computation for the bounded homotopy functors lives
in `Bounded.Map.Computation`.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

namespace Homotopy

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D]

/-- Mapping a bounded-below cochain complex termwise and then passing to the homotopy category
agrees with first passing to the homotopy category and then applying the induced functor. -/
@[stacks 014X "bounded-below cochain-to-homotopy comparison"]
def Plus.quotientIso (F : C ⥤ D) [F.Additive] :
    F.mapCochainComplexPlus ⋙ HomotopyCategory.Plus.quotient D ≅
      HomotopyCategory.Plus.quotient C ⋙ F.mapHomotopyCategoryPlus :=
  ((HomotopyCategory.Plus.fullyFaithfulι D).whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (CochainComplex.Plus.ι C)
      (F.mapHomotopyCategoryFactors (up ℤ)).symm)

/-- Mapping a bounded-above cochain complex termwise and then passing to the homotopy category
agrees with first passing to the homotopy category and then applying the induced functor. -/
@[stacks 014X "bounded-above cochain-to-homotopy comparison"]
def Minus.quotientIso (F : C ⥤ D) [F.Additive] :
    Functor.Cochain.Minus.map F ⋙ HomotopyCategory.Minus.quotient D ≅
      HomotopyCategory.Minus.quotient C ⋙ F.mapHomotopyCategoryMinus :=
  ((HomotopyCategory.Minus.fullyFaithfulι D).whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (CochainComplex.Minus.ι C)
      (F.mapHomotopyCategoryFactors (up ℤ)).symm)

/-- Mapping a bounded cochain complex termwise and then passing to the homotopy category agrees
with first passing to the homotopy category and then applying the induced functor. -/
@[stacks 014X "bounded cochain-to-homotopy comparison"]
def Bounded.quotientIso (F : C ⥤ D) [F.Additive] :
    Functor.Cochain.Bounded.map F ⋙ HomotopyCategory.Bounded.quotient D ≅
      HomotopyCategory.Bounded.quotient C ⋙ F.mapHomotopyCategoryBounded :=
  ((HomotopyCategory.Bounded.fullyFaithfulι D).whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (CochainComplex.Bounded.ι C)
      (F.mapHomotopyCategoryFactors (up ℤ)).symm)

section Checks

variable [HasZeroObject C] [HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  (F : C ⥤ D) [F.Additive]

end Checks

end Homotopy

end Functor

end CategoryTheory
