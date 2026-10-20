module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger

/-!
# Schlessinger's condition (H4) for set-valued functors

Preservation of fibre-product squares along surjections is equivalent to
bijectivity of the comparison with the fibre product of types and to the
Rim-Schlessinger condition for the category-of-elements projection.
-/

@[expose] public section

open CategoryTheory Limits

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- The induced map `F.obj P → Types.PullbackObj (F.map f1) (F.map f2)` associated to a
fibre-product square in `ArtinianLocalAlgCat Λ k`. -/
def schlessingerH4Comparison (F : ArtinianLocalAlgCat Λ k ⥤ Type v)
    {A A1 A2 P : ArtinianLocalAlgCat Λ k}
    (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) (π1 : P ⟶ A1) (π2 : P ⟶ A2)
    (h : IsPullback π1 π2 f1 f2) :
    F.obj P → Types.PullbackObj (F.map f1) (F.map f2) :=
  (PullbackCone.mk (F.map π1) (F.map π2) (F.map_commSq h.toCommSq).w).toPullbackObj

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

/-- The category-of-elements projection of a set-valued functor satisfies the
Rim-Schlessinger condition exactly when the functor satisfies Schlessinger's (H4). -/
theorem hasRimSchlessinger_iff_hasSchlessingerH4
    (F : ArtinianLocalAlgCat Λ k ⥤ Type v) :
    HasRimSchlessinger (CategoryOfElements.π F) ↔ HasSchlessingerH4 F := sorry

end CategoryTheory.Functor
