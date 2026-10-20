/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.EssentialImage
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Versal
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber

/-!
# Quasi-initiality of versal formal objects

A versal formal object of a predeformation category admits a morphism to every
formal object.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace CategoryTheory.BasedFunctor

/-- A based morphism from the restricted coyoneda of a complete local algebra into a
predeformation category is essentially surjective on residue fibres. -/
instance essSurj_residue_of_predeformation {R : CompleteLocalAlgCat Λ k}
    [Functor.IsPredeformationCategory p]
    (φ : BasedCategory.ofFunctor (CompleteLocalAlgCat.identityProjection R) ⥤ᵇ
      BasedCategory.ofFunctor p) :
    (φ.fiberFunctor (ArtinianLocalAlgCat.residue Λ k)).EssSurj :=
  sorry

end CategoryTheory.BasedFunctor

namespace FormalObject

/-- A versal formal object of a predeformation category admits a morphism to every
formal object. -/
theorem exists_hom_of_isVersal [Functor.IsPredeformationCategory p]
    (ξ : FormalObject p) [IsVersal ξ] (η : FormalObject p) :
    Nonempty (ξ ⟶ η) :=
  sorry

end FormalObject
