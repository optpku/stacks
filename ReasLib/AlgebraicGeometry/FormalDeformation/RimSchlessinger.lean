/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal

/-!
# The Rim-Schlessinger condition

Cospans whose second projected algebra map is surjective have pullbacks in the
total category that remain pullbacks after projection to `ArtinianLocalAlgCat`.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- A functor `p : F ⥤ ArtinianLocalAlgCat Λ k` satisfies the Rim-Schlessinger condition
(RS) if it is cofibered in groupoids and every cospan in `F` lying over a cospan in
`ArtinianLocalAlgCat Λ k` with surjective `A₂ → A` admits a fibre product in `F` whose
image square is a pullback in `ArtinianLocalAlgCat Λ k`. -/
class HasRimSchlessinger (p : F ⥤ ArtinianLocalAlgCat Λ k) : Prop where
  [isCofiberedInGroupoids : IsFibered.InGroupoids p.op]
  exists_pullback : ∀ {x x1 x2 : F} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x),
    Function.Surjective (p.map f2).hom →
      ∃ (w : F) (π1 : w ⟶ x1) (π2 : w ⟶ x2),
        IsPullback π1 π2 f1 f2 ∧
          IsPullback (p.map π1) (p.map π2) (p.map f1) (p.map f2)

attribute [instance] HasRimSchlessinger.isCofiberedInGroupoids

/-- The identity functor on `ArtinianLocalAlgCat Λ k` satisfies (RS). -/
instance instHasRimSchlessingerId :
    HasRimSchlessinger (𝟭 (ArtinianLocalAlgCat Λ k)) := sorry

/-- The Rim-Schlessinger condition is cofiberedness in groupoids together with existence of
fibre products lying over ring-level fibre products along a surjection. -/
theorem hasRimSchlessinger_spec (p : F ⥤ ArtinianLocalAlgCat Λ k) :
    HasRimSchlessinger p ↔
      IsFibered.InGroupoids p.op ∧
        ∀ {x x1 x2 : F} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x),
          Function.Surjective (p.map f2).hom →
            ∃ (w : F) (π1 : w ⟶ x1) (π2 : w ⟶ x2),
              IsPullback π1 π2 f1 f2 ∧
                IsPullback (p.map π1) (p.map π2) (p.map f1) (p.map f2) := sorry

end CategoryTheory.Functor
