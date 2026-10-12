/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SchlessingerH4

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

/- Schlessinger's condition (H4) on set-valued functors. -/
#check (CategoryTheory.Functor.HasSchlessingerH4 :
  (ArtinianLocalAlgCat Λ k ⥤ Type v) → Prop)

/- The comparison-map characterization of Schlessinger's condition (H4). -/
#check (CategoryTheory.Functor.hasSchlessingerH4_iff :
  ∀ (F : ArtinianLocalAlgCat Λ k ⥤ Type v), HasSchlessingerH4 F ↔
      ∀ {A A1 A2 P : ArtinianLocalAlgCat Λ k} (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
        (π1 : P ⟶ A1) (π2 : P ⟶ A2) (h : IsPullback π1 π2 f1 f2),
        Function.Surjective f2.hom →
          Function.Bijective (schlessingerH4Comparison F f1 f2 π1 π2 h))

end CategoryTheory.Functor
