/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Cover
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pushforward

/-!
# Relative flatness and affine pushforward

Pushforward along an affine morphism preserves and reflects relative flatness of
quasi-coherent scheme modules.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A quasi-coherent scheme module is flat over a base if and only if its pushforward along an
affine morphism is flat over that base. -/
theorem flatOver_iff_pushforward_flatOver_of_isAffineHom
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [IsAffineHom f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    flatOver ℱ (f ≫ g) ↔ flatOver ((Scheme.Modules.pushforward f).obj ℱ) g := sorry

end AlgebraicGeometry.Scheme.Modules
