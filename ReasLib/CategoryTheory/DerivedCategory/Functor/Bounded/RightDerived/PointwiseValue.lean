module

public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Quotient
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Functor.Right
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pointwise Right-Derived Values of Bounded-Below Complexes

This file packages the stable composite from bounded-below cochain complexes through the
homotopy quotient to pointwise right-derived values. It does not choose a localization model or
a total derived functor, so applications that only use pointwise existence need not carry either
piece of auxiliary data.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.RightDerived.Bounded

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {D : Type u₂} [Category.{v₂} D]

/-- Pointwise right-derived values of a functor on the bounded-below homotopy category,
assembled as a functor of bounded-below cochain complexes. -/
@[stacks 05SA "bounded-below pointwise right-derived value functor"]
noncomputable abbrev pointwiseValueFunctor
    (G : HomotopyCategory.Plus A ⥤ D)
    [G.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)] :
    CochainComplex.Plus A ⥤ D :=
  HomotopyCategory.Plus.quotient A ⋙
    RightDerived.Value.functor G (HomotopyCategory.Plus.quasiIso A)

namespace pointwiseValueFunctor

/-- On objects, the bounded-below pointwise value functor is the pointwise right-derived value
of the homotopy quotient. -/
@[simp, stacks 05SA "bounded-below pointwise right-derived value computation"]
theorem obj
    (G : HomotopyCategory.Plus A ⥤ D)
    [G.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    (K : CochainComplex.Plus A) :
    (pointwiseValueFunctor G).obj K =
      RightDerived.Value.obj G (HomotopyCategory.Plus.quasiIso A)
        ((HomotopyCategory.Plus.quotient A).obj K) := sorry

/-- On morphisms, the bounded-below pointwise value functor is the canonical map between
pointwise right-derived values induced by the homotopy quotient. -/
@[simp, stacks 05SA "bounded-below pointwise right-derived value computation"]
theorem map
    (G : HomotopyCategory.Plus A ⥤ D)
    [G.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    (pointwiseValueFunctor G).map f =
      RightDerived.Value.map G (HomotopyCategory.Plus.quasiIso A)
        ((HomotopyCategory.Plus.quotient A).map f) := sorry

end pointwiseValueFunctor

/-- The pointwise right-derived value of `G` at a bounded-below cochain complex. -/
@[stacks 05SA "bounded-below pointwise right-derived value"]
noncomputable abbrev pointwiseValue
    (G : HomotopyCategory.Plus A ⥤ D)
    [G.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    (K : CochainComplex.Plus A) : D :=
  (pointwiseValueFunctor G).obj K

/-- The map on bounded-below pointwise right-derived values induced by a cochain map. -/
@[stacks 05SA "bounded-below pointwise right-derived value map"]
noncomputable abbrev pointwiseValueMap
    (G : HomotopyCategory.Plus A ⥤ D)
    [G.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    pointwiseValue G K ⟶ pointwiseValue G L :=
  (pointwiseValueFunctor G).map f

/-- The pointwise right-derived value map of an identity cochain map is an identity. -/
@[simp, stacks 05SA "identity of bounded-below pointwise right-derived values"]
theorem pointwiseValueMap_id
    (G : HomotopyCategory.Plus A ⥤ D)
    [G.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    (K : CochainComplex.Plus A) :
    pointwiseValueMap G (𝟙 K) = 𝟙 (pointwiseValue G K) := sorry

/-- Pointwise right-derived value maps preserve composition of cochain maps. -/
@[reassoc, stacks 05SA "composition of bounded-below pointwise right-derived values"]
theorem pointwiseValueMap_comp
    (G : HomotopyCategory.Plus A ⥤ D)
    [G.HasPointwiseRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]
    {K L M : CochainComplex.Plus A} (f : K ⟶ L) (g : L ⟶ M) :
    pointwiseValueMap G (f ≫ g) = pointwiseValueMap G f ≫ pointwiseValueMap G g := sorry

end CategoryTheory.Functor.RightDerived.Bounded
