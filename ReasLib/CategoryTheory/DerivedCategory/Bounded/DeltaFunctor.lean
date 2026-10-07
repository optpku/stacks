module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Exact
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Abelian
public import ReasLib.CategoryTheory.DerivedCategory.BoundedLocalization.Computation
public import ReasLib.CategoryTheory.DerivedCategory.DeltaFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Delta Functor for Bounded-Below Derived Localization

This leaf refines the canonical localization of all cochain complexes to the
bounded-below setting.  Its data are built from Mathlib's
`DerivedCategory.Plus.Q` and the ambient short-exact-sequence boundary map;
only the two coherence propositions remain proof debt.
-/

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.Plus

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Stacks 0159: the connecting morphism in the bounded-below derived
category associated to a short exact sequence of bounded-below cochain
complexes. -/
@[stacks 0159]
noncomputable def Delta.connecting
    {S : ShortComplex (CochainComplex.Plus C)} (hS : S.ShortExact) :
    _root_.DerivedCategory.Plus.Q.obj S.X₃ ⟶
      (_root_.DerivedCategory.Plus.Q.obj S.X₁)⟦(1 : ℤ)⟧ :=
  ObjectProperty.homMk
    ((CategoryTheory.DerivedCategory.Plus.Qh.compInclusionIso C).hom.app S.X₃ ≫
      (CategoryTheory.DerivedCategory.Delta.functor C).δ
        (hS.map_of_exact (CochainComplex.Plus.ι C)) ≫
        ((CategoryTheory.DerivedCategory.Plus.Qh.compInclusionIso C).inv.app S.X₁)⟦(1 : ℤ)⟧' ≫
          ((Functor.commShiftIso
            (_root_.DerivedCategory.Plus.ι :
              _root_.DerivedCategory.Plus C ⥤ _root_.DerivedCategory C)
            (1 : ℤ)).inv.app (_root_.DerivedCategory.Plus.Q.obj S.X₁)))

/-- The triangle induced by `Delta.connecting` is distinguished. -/
@[stacks 0159]
theorem Delta.triangle_distinguished
    {S : ShortComplex (CochainComplex.Plus C)} (hS : S.ShortExact) :
    Triangle.mk (_root_.DerivedCategory.Plus.Q.map S.f)
      (_root_.DerivedCategory.Plus.Q.map S.g) (Delta.connecting C hS) ∈
        distTriang (_root_.DerivedCategory.Plus C) := sorry

/-- The bounded-below connecting morphisms are natural in maps of short exact
sequences. -/
@[stacks 0159]
theorem Delta.naturality
    {S T : ShortComplex (CochainComplex.Plus C)}
    (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T) :
    CommSq (_root_.DerivedCategory.Plus.Q.map f.τ₃) (Delta.connecting C hS)
      (Delta.connecting C hT)
      ((_root_.DerivedCategory.Plus.Q.map f.τ₁)⟦(1 : ℤ)⟧') := sorry

/-- Lemma 13.20.3 (1): the bounded-below derived localization of cochain
complexes, equipped with its canonical delta-functor structure. -/
@[stacks 0159]
noncomputable def Delta.functor :
    DeltaFunctor (CochainComplex.Plus C) (_root_.DerivedCategory.Plus C) where
  toFunctor := _root_.DerivedCategory.Plus.Q
  additive := inferInstance
  δ := fun {_} hS ↦ Delta.connecting C hS
  map_distinguished := fun {_} hS ↦
    Delta.triangle_distinguished C hS
  δ_naturality := fun {_ _} hS hT f ↦
    Delta.naturality C hS hT f

/-- The underlying functor of `Delta.functor` is the canonical
bounded-below derived localization. -/
@[simp, stacks 0159]
theorem Delta.functor_toFunctor :
    (Delta.functor C).toFunctor = _root_.DerivedCategory.Plus.Q := sorry

/-- The connecting morphism of the bounded-below localization delta functor is
`Delta.connecting`. -/
@[simp, stacks 0159]
theorem Delta.functor_δ
    {S : ShortComplex (CochainComplex.Plus C)} (hS : S.ShortExact) :
    (Delta.functor C).δ hS = Delta.connecting C hS := sorry

end CategoryTheory.DerivedCategory.Plus
