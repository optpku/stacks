/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme.RimSchlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory.Over
import StacksCheckRecall

/-!
# Rim-Schlessinger condition for schemes

Example 93.9.1 satisfies (RS), so each residue-fibre slice `Def_X` is a
deformation category.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Lemma 93.9.2 (1)
Example 93.9.1 satisfies the Rim-Schlessinger condition (RS). -/
@[stacks 0DY8] #check (FlatSchemeCat.instHasRimSchlessinger_forget Λ k :
  HasRimSchlessinger (FlatSchemeCat.forget Λ k))

variable (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))

/- Lemma 93.9.2 (2)
In particular, `Def_X` is a deformation category for any scheme `X` over `k`. -/
@[stacks 0DY8] #check (CategoryTheory.Functor.instIsDeformationCategory_overForget
  (FlatSchemeCat.forget Λ k) (FlatSchemeCat.residueObj Λ k X hX) :
  IsDeformationCategory
    (Over.forget (Fiber.fiberInclusion.obj (FlatSchemeCat.residueObj Λ k X hX)) ⋙
      FlatSchemeCat.forget Λ k))
