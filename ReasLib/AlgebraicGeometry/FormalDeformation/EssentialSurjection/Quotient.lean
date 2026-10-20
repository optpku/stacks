/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.EssentialSurjection
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.InfinitesimalQuotient

/-!
# Essential surjectivity on infinitesimal quotients

Essential surjectivity of a residue-compatible Artinian local algebra morphism
is detected both on maximal-ideal square quotients and on relative infinitesimal
quotients.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- A morphism is an essential surjection exactly when its induced square-quotient map is. -/
theorem isEssentialSurjection_iff_modSquare {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    IsEssentialSurjection f ↔ IsEssentialSurjection (modSquareMap f) := sorry

/-- A morphism is an essential surjection exactly when its induced relative-quotient map is. -/
theorem isEssentialSurjection_iff_modRelative {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    IsEssentialSurjection f ↔ IsEssentialSurjection (modRelativeMap f) := sorry

/-- Essential surjectivity of the square-quotient map is equivalent to that of the relative map. -/
theorem isEssentialSurjection_modSquare_iff_modRelative {B A : ArtinianLocalAlgCat Λ k}
    (f : B ⟶ A) :
    IsEssentialSurjection (modSquareMap f) ↔ IsEssentialSurjection (modRelativeMap f) :=
  sorry

end ArtinianLocalAlgCat
