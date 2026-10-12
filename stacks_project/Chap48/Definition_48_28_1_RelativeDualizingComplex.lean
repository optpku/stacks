/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Relative

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

/- Compatibility check for the source-facing API. -/
#check (AlgebraicGeometry.Scheme.RelativeDualizingComplex :
  {X S : Scheme.{u}} → (f : X ⟶ S) → [Flat f] → [LocallyOfFinitePresentation f] →
    (W : (pullback f f).Opens) → (δ : X ⟶ W.toScheme) → [IsClosedImmersion δ] →
    (hδ : δ ≫ W.ι = pullback.diagonal f) →
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)] →
    [MonoidalCategory (RingedSpace.ModuleDerived W.toScheme.toRingedSpace)] →
    [(RingedSpace.moduleDerivedPushforward δ.toShHom).LaxMonoidal] →
    (H : MonoidalClosed (RingedSpace.ModuleDerived W.toScheme.toRingedSpace)) → Type (u + 1))
