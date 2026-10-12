/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

/-!
# Fiber-support subschemes for modules on schemes

This file provides a finitely presented closed subscheme realizing the support of a
finite-type quasicoherent module on a chosen fiber.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- For a finite-type morphism of affine schemes and a finite-type quasicoherent module,
there is a finitely presented closed subscheme whose fiber over a chosen point is the support
of the module pulled back to that fiber. -/
theorem exists_fiberSupportSubscheme {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) [Scheme.Hom.FiniteType f] (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    [ℱ.IsFiniteType] (x : X) :
    ∃ I : X.IdealSheafData, ∃ _ : Scheme.Hom.FinitePresentation I.subschemeι,
      ∃ 𝒢 : I.subscheme.Modules, ∃ _ : 𝒢.IsQuasicoherent, ∃ _ : 𝒢.IsFiniteType,
        Nonempty ((Scheme.Modules.pushforward I.subschemeι).obj 𝒢 ≅ ℱ) ∧
          ((I.comap (f.fiberι (f x))).support : Set (f.fiber (f x))) =
            moduleSupport ((Scheme.Modules.pullback (f.fiberι (f x))).obj ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules
