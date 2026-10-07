module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Basic
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Values of Bounded-Below Right Derived Functors

This file packages the value of a total right-derived functor on a bounded-below complex for an
arbitrary localization model. It is independent of any resolution or spectral-sequence
construction; the derived-category cohomology specialization lives in `RightDerived.Cohomology`.
The functorial owner is exposed first, so object and morphism computations use the ordinary
`Functor` API.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived.Bounded

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]

/-- The bounded-below value functor obtained by composing the homotopy quotient,
the chosen localization model, and a total right-derived functor. -/
@[stacks 015H "bounded-below total right-derived value functor"]
noncomputable abbrev valueFunctor
    {D : Type u₂} [Category.{v₂} D]
    (G : HomotopyCategory.Plus A ⥤ D)
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [G.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)] :
    CochainComplex.Plus A ⥤ D :=
  HomotopyCategory.Plus.quotient A ⋙ Q ⋙
    G.totalRightDerived Q (HomotopyCategory.Plus.quasiIso A)

namespace valueFunctor

/-- The bounded-below value functor is computed on objects by the quotient, localization model,
and total right-derived functor. -/
@[simp, stacks 015H "bounded-below value functor object computation"]
theorem obj
    {D : Type u₂} [Category.{v₂} D]
    (G : HomotopyCategory.Plus A ⥤ D)
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [G.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (K : CochainComplex.Plus A) :
    (valueFunctor G Q).obj K =
      (G.totalRightDerived Q (HomotopyCategory.Plus.quasiIso A)).obj
        (Q.obj ((HomotopyCategory.Plus.quotient A).obj K)) := sorry

/-- The bounded-below value functor is computed on morphisms by the quotient, localization model,
and total right-derived functor. -/
@[simp, stacks 015H "bounded-below value functor morphism computation"]
theorem map
    {D : Type u₂} [Category.{v₂} D]
    (G : HomotopyCategory.Plus A ⥤ D)
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [G.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    (valueFunctor G Q).map f =
      (G.totalRightDerived Q (HomotopyCategory.Plus.quasiIso A)).map
        (Q.map ((HomotopyCategory.Plus.quotient A).map f)) := sorry

end valueFunctor

/-- The value at `K` of the total right derived functor of `G`, computed using the
bounded-below localization model `Q`. -/
@[stacks 015H "bounded-below total right-derived value"]
noncomputable abbrev value
    {D : Type u₂} [Category.{v₂} D]
    (G : HomotopyCategory.Plus A ⥤ D)
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [G.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (K : CochainComplex.Plus A) : D :=
  (valueFunctor G Q).obj K

/-- The morphism induced on bounded-below right-derived values by a cochain map. -/
@[stacks 015H "bounded-below total right-derived value map"]
noncomputable abbrev valueMap
    {D : Type u₂} [Category.{v₂} D]
    (G : HomotopyCategory.Plus A ⥤ D)
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [G.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    {K L : CochainComplex.Plus A} (f : K ⟶ L) :
    value G Q K ⟶ value G Q L :=
  (valueFunctor G Q).map f

/-- The value map of an identity cochain morphism is an identity. -/
@[simp, stacks 015H "bounded-below value map identity"]
theorem valueMap_id
    {D : Type u₂} [Category.{v₂} D]
    (G : HomotopyCategory.Plus A ⥤ D)
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [G.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (K : CochainComplex.Plus A) :
    valueMap G Q (𝟙 K) = 𝟙 (value G Q K) := sorry

/-- The value map of a composite cochain morphism is the composite of the value maps. -/
@[reassoc, stacks 015H "bounded-below value map composition"]
theorem valueMap_comp
    {D : Type u₂} [Category.{v₂} D]
    (G : HomotopyCategory.Plus A ⥤ D)
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    [G.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    {K L M : CochainComplex.Plus A} (f : K ⟶ L) (g : L ⟶ M) :
    valueMap G Q (f ≫ g) = valueMap G Q f ≫ valueMap G Q g := sorry

end CategoryTheory.Functor.RightDerived.Bounded
