module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal

/-!
# Schlessinger's condition (H4)

For a functor `F : ArtinianLocalAlgCat Λ k ⥤ Type v`, condition (H4) says that
`F` sends fibre-product squares in `ArtinianLocalAlgCat Λ k` along a surjection
to fibre-product squares in `Type`. Equivalently, the induced comparison
`F.obj P → Types.PullbackObj (F.map f1) (F.map f2)` is bijective.
-/

@[expose] public section

open CategoryTheory Limits

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- Images of a fibre-product object under the two projections agree after applying `F`
to the cospan. -/
theorem schlessingerH4Comparison_mem (F : ArtinianLocalAlgCat Λ k ⥤ Type v)
    {A A1 A2 P : ArtinianLocalAlgCat Λ k}
    (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) (π1 : P ⟶ A1) (π2 : P ⟶ A2)
    (h : IsPullback π1 π2 f1 f2) (x : F.obj P) :
    F.map f1 (F.map π1 x) = F.map f2 (F.map π2 x) := sorry

/-- The induced map `F.obj P → Types.PullbackObj (F.map f1) (F.map f2)` associated to a
fibre-product square in `ArtinianLocalAlgCat Λ k`. -/
def schlessingerH4Comparison (F : ArtinianLocalAlgCat Λ k ⥤ Type v)
    {A A1 A2 P : ArtinianLocalAlgCat Λ k}
    (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) (π1 : P ⟶ A1) (π2 : P ⟶ A2)
    (h : IsPullback π1 π2 f1 f2) :
    F.obj P → Types.PullbackObj (F.map f1) (F.map f2) :=
  fun x ↦ ⟨⟨F.map π1 x, F.map π2 x⟩, schlessingerH4Comparison_mem F f1 f2 π1 π2 h x⟩

/-- The Schlessinger (H4) comparison map sends `x` to the pair `(F.map π1 x, F.map π2 x)`. -/
theorem schlessingerH4Comparison_spec (F : ArtinianLocalAlgCat Λ k ⥤ Type v)
    {A A1 A2 P : ArtinianLocalAlgCat Λ k}
    (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) (π1 : P ⟶ A1) (π2 : P ⟶ A2)
    (h : IsPullback π1 π2 f1 f2) (x : F.obj P) :
    (schlessingerH4Comparison F f1 f2 π1 π2 h x).1 = (F.map π1 x, F.map π2 x) := sorry

/-- Schlessinger's condition (H4): `F` preserves fibre-product squares in
`ArtinianLocalAlgCat Λ k` along a surjection. -/
def HasSchlessingerH4 (F : ArtinianLocalAlgCat Λ k ⥤ Type v) : Prop :=
  ∀ {A A1 A2 P : ArtinianLocalAlgCat Λ k} (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    (π1 : P ⟶ A1) (π2 : P ⟶ A2),
    Function.Surjective f2.hom →
      IsPullback π1 π2 f1 f2 →
        IsPullback (F.map π1) (F.map π2) (F.map f1) (F.map f2)

/-- Schlessinger's (H4) is equivalent to bijectivity of the induced comparison
`F.obj P → Types.PullbackObj (F.map f1) (F.map f2)` along a surjection. -/
theorem hasSchlessingerH4_iff (F : ArtinianLocalAlgCat Λ k ⥤ Type v) :
    HasSchlessingerH4 F ↔
      ∀ {A A1 A2 P : ArtinianLocalAlgCat Λ k} (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
        (π1 : P ⟶ A1) (π2 : P ⟶ A2) (h : IsPullback π1 π2 f1 f2),
        Function.Surjective f2.hom →
          Function.Bijective (schlessingerH4Comparison F f1 f2 π1 π2 h) := sorry

end CategoryTheory.Functor
