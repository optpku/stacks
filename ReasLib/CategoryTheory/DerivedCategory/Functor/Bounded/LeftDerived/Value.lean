module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Above.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Values of Bounded-Above Left Derived Functors

This leaf packages the value of a total left-derived functor on a bounded-above
complex for an arbitrary localization model.  The functorial owner is exposed
first; `value` and `valueMap` are its object and morphism projections.  This
keeps computation and naturality in the complex available without committing
the generic API to a particular derived-category target.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.LeftDerived.Bounded

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]

/-- The bounded-above value functor obtained by composing the homotopy quotient,
the chosen localization model, and a total left-derived functor. -/
@[stacks 015H "bounded-above total left-derived value functor"]
noncomputable abbrev valueFunctor
    {D : Type u₂} [Category.{v₂} D]
    (G : HomotopyCategory.Minus A ⥤ D)
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Minus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Minus.quasiIso A)]
    [G.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)] :
    CochainComplex.Minus A ⥤ D :=
  HomotopyCategory.Minus.quotient A ⋙ Q ⋙
    G.totalLeftDerived Q (HomotopyCategory.Minus.quasiIso A)

namespace valueFunctor

/-- The bounded-above value functor is computed on objects by the quotient, localization model,
and total left-derived functor. -/
@[simp, stacks 015H "bounded-above value functor object computation"]
theorem obj
    {D : Type u₂} [Category.{v₂} D]
    (G : HomotopyCategory.Minus A ⥤ D)
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Minus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Minus.quasiIso A)]
    [G.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (K : CochainComplex.Minus A) :
    (valueFunctor G Q).obj K =
      (G.totalLeftDerived Q (HomotopyCategory.Minus.quasiIso A)).obj
        (Q.obj ((HomotopyCategory.Minus.quotient A).obj K)) := sorry

/-- The bounded-above value functor is computed on morphisms by the quotient, localization model,
and total left-derived functor. -/
@[simp, stacks 015H "bounded-above value functor morphism computation"]
theorem map
    {D : Type u₂} [Category.{v₂} D]
    (G : HomotopyCategory.Minus A ⥤ D)
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Minus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Minus.quasiIso A)]
    [G.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    {K L : CochainComplex.Minus A} (f : K ⟶ L) :
    (valueFunctor G Q).map f =
      (G.totalLeftDerived Q (HomotopyCategory.Minus.quasiIso A)).map
        (Q.map ((HomotopyCategory.Minus.quotient A).map f)) := sorry

end valueFunctor

/-- The value at `K` of the total bounded-above left-derived functor of `G`,
computed using the localization model `Q`. -/
@[stacks 015H "bounded-above total left-derived value"]
noncomputable abbrev value
    {D : Type u₂} [Category.{v₂} D]
    (G : HomotopyCategory.Minus A ⥤ D)
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Minus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Minus.quasiIso A)]
    [G.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (K : CochainComplex.Minus A) : D :=
  (valueFunctor G Q).obj K

/-- The morphism induced on bounded-above left-derived values by a cochain map. -/
@[stacks 015H "bounded-above total left-derived value map"]
noncomputable abbrev valueMap
    {D : Type u₂} [Category.{v₂} D]
    (G : HomotopyCategory.Minus A ⥤ D)
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Minus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Minus.quasiIso A)]
    [G.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    {K L : CochainComplex.Minus A} (f : K ⟶ L) :
    value G Q K ⟶ value G Q L :=
  (valueFunctor G Q).map f

/-- The value map of an identity cochain morphism is an identity. -/
@[simp, stacks 015H "bounded-above value map identity"]
theorem valueMap_id
    {D : Type u₂} [Category.{v₂} D]
    (G : HomotopyCategory.Minus A ⥤ D)
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Minus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Minus.quasiIso A)]
    [G.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    (K : CochainComplex.Minus A) :
    valueMap G Q (𝟙 K) = 𝟙 (value G Q K) := sorry

/-- The value map of a composite cochain morphism is the composite of the value maps. -/
@[reassoc, stacks 015H "bounded-above value map composition"]
theorem valueMap_comp
    {D : Type u₂} [Category.{v₂} D]
    (G : HomotopyCategory.Minus A ⥤ D)
    {E : Type u₃} [Category.{v₃} E]
    (Q : HomotopyCategory.Minus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Minus.quasiIso A)]
    [G.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A)]
    {K L M : CochainComplex.Minus A} (f : K ⟶ L) (g : L ⟶ M) :
    valueMap G Q (f ≫ g) = valueMap G Q f ≫ valueMap G Q g := sorry

end CategoryTheory.Functor.LeftDerived.Bounded
