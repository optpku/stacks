/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SchemeMorphism
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory.Over

/-!
# Rim-Schlessinger condition for morphisms of schemes

The projection from flat scheme morphisms over Artinian local algebras to their
base algebras satisfies the Rim-Schlessinger condition. Its residue-object
slices are deformation categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FlatSchemeMorphismCat

/-- The projection from deformations of a scheme morphism over the residue field
to their Artinian local base algebras. -/
abbrev deformationForget (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    deformation Λ k X Y f hX hY hf ⥤ ArtinianLocalAlgCat Λ k :=
  Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X Y f hX hY hf)) ⋙ forget Λ k

/-- The deformation projection is the slice-forgetful functor followed by the
projection to the base algebra. -/
theorem deformationForget_eq (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    deformationForget Λ k X Y f hX hY hf =
      Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X Y f hX hY hf)) ⋙
        forget Λ k := rfl

/-- The projection from flat scheme morphisms over Artinian local algebras to
their base algebras satisfies the Rim-Schlessinger condition. -/
instance instHasRimSchlessinger_forget : HasRimSchlessinger (forget Λ k) := sorry

/-- The residue-object slice associated to any scheme morphism over the residue
field is a deformation category under its projection to the base algebra. -/
instance instIsDeformationCategory_deformationForget
    (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    IsDeformationCategory (deformationForget Λ k X Y f hX hY hf) :=
  instIsDeformationCategory_overForget (forget Λ k) (residueObj Λ k X Y f hX hY hf)

end FlatSchemeMorphismCat
