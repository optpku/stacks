/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.Restriction

/-!
# Restriction functor of scheme deformation categories
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open scoped AlgebraicGeometry BasedFunctor

noncomputable section

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

variable (X : Scheme.{u})
  (hX : X ⟶ Spec (CommRingCat.of k))
  (U : X.Opens)

/- Lemma 93.9.6
In Example 93.9.1 let `X` be a scheme over `k`. Let `U ⊂ X` be an open
subscheme. There is a natural functor from the deformation category of `X`
to the deformation category of `U`. -/
@[stacks 0DYW] #check (FlatSchemeCat.restrictOpen Λ k
  X hX U :
  BasedCategory.ofFunctor
      (Over.forget (Fiber.fiberInclusion.obj (FlatSchemeCat.residueObj Λ k X hX)) ⋙
        FlatSchemeCat.forget Λ k) ⥤ᵇ
    BasedCategory.ofFunctor
      (Over.forget (Fiber.fiberInclusion.obj
          (FlatSchemeCat.residueObj Λ k U.toScheme (U.ι ≫ hX))) ⋙
        FlatSchemeCat.forget Λ k))

end
