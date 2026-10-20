/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.TwoAffineOpenCover
public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections

/-!
# Deformation categories of a two-chart affine cover

Structure morphisms of the open subschemes over `k`, and the named deformation
categories of the scheme, its affine opens, and the section rings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

variable {X : Scheme.{u}}

/-- The structure morphism of `U₁` over `k`. -/
abbrev structureHom₁ (c : TwoAffineOpenCover X)
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier)) :
    c.U₁.toScheme ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier) :=
  c.U₁.ι ≫ hX

/-- The structure morphism of `U₂` over `k`. -/
abbrev structureHom₂ (c : TwoAffineOpenCover X)
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier)) :
    c.U₂.toScheme ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier) :=
  c.U₂.ι ≫ hX

/-- The structure morphism of `U₁ ⊓ U₂` over `k`. -/
abbrev structureHomInf (c : TwoAffineOpenCover X)
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier)) :
    (c.U₁ ⊓ c.U₂).toScheme ⟶
      Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier) :=
  (c.U₁ ⊓ c.U₂).ι ≫ hX

/-- The canonical `k`-algebra structure on `Γ(X, U₁)` induced by `hX`. -/
abbrev algebraRing₁ (c : TwoAffineOpenCover X)
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier)) :
    Algebra k Γ(X, c.U₁) :=
  hX.sectionsAlgebraOverSpec c.U₁

/-- The canonical `k`-algebra structure on `Γ(X, U₂)` induced by `hX`. -/
abbrev algebraRing₂ (c : TwoAffineOpenCover X)
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier)) :
    Algebra k Γ(X, c.U₂) :=
  hX.sectionsAlgebraOverSpec c.U₂

/-- The canonical `k`-algebra structure on `Γ(X, U₁ ⊓ U₂)` induced by `hX`. -/
abbrev algebraRingInf (c : TwoAffineOpenCover X)
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier)) :
    Algebra k Γ(X, c.U₁ ⊓ c.U₂) :=
  hX.sectionsAlgebraOverSpec (c.U₁ ⊓ c.U₂)

/-- The deformation category `Def_{U₁}` of the first affine open. -/
abbrev deformationCategory_U₁ (c : TwoAffineOpenCover X)
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier)) :=
  FlatSchemeCat.deformationCategory Λ k c.U₁.toScheme (structureHom₁ Λ k c hX)

/-- `deformationCategory_U₁` is the Over-slice at the residue object `(k, U₁)`. -/
theorem deformationCategory_U₁_spec (c : TwoAffineOpenCover X)
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier)) :
    deformationCategory_U₁ Λ k c hX =
      Over (Fiber.fiberInclusion.obj
        (FlatSchemeCat.residueObj Λ k c.U₁.toScheme (structureHom₁ Λ k c hX))) :=
  rfl

/-- The deformation category `Def_{U₂}` of the second affine open. -/
abbrev deformationCategory_U₂ (c : TwoAffineOpenCover X)
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier)) :=
  FlatSchemeCat.deformationCategory Λ k c.U₂.toScheme (structureHom₂ Λ k c hX)

/-- `deformationCategory_U₂` is the Over-slice at the residue object `(k, U₂)`. -/
theorem deformationCategory_U₂_spec (c : TwoAffineOpenCover X)
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier)) :
    deformationCategory_U₂ Λ k c hX =
      Over (Fiber.fiberInclusion.obj
        (FlatSchemeCat.residueObj Λ k c.U₂.toScheme (structureHom₂ Λ k c hX))) :=
  rfl

/-- The deformation category `Def_{U₁₂}` of the overlap. -/
abbrev deformationCategory_inf (c : TwoAffineOpenCover X)
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier)) :=
  FlatSchemeCat.deformationCategory Λ k (c.U₁ ⊓ c.U₂).toScheme (structureHomInf Λ k c hX)

/-- `deformationCategory_inf` is the Over-slice at the residue object `(k, U₁ ⊓ U₂)`. -/
theorem deformationCategory_inf_spec (c : TwoAffineOpenCover X)
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier)) :
    deformationCategory_inf Λ k c hX =
      Over (Fiber.fiberInclusion.obj
        (FlatSchemeCat.residueObj Λ k (c.U₁ ⊓ c.U₂).toScheme (structureHomInf Λ k c hX))) :=
  rfl

/-- The deformation category `Def_{P₁}` of the first section ring. -/
abbrev deformationCategory_ring₁ (c : TwoAffineOpenCover X)
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier)) :=
  let P : CommAlgCat k := hX.sectionsAlgOverSpec c.U₁
  FlatAlgebraCat.deformationCategory Λ k P

/-- `deformationCategory_ring₁` is the Over-slice at the residue object `(k, P₁)`. -/
theorem deformationCategory_ring₁_spec (c : TwoAffineOpenCover X)
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier)) :
    deformationCategory_ring₁ Λ k c hX =
      (let P : CommAlgCat k := hX.sectionsAlgOverSpec c.U₁
       Over (Fiber.fiberInclusion.obj (FlatAlgebraCat.residueObj Λ k P))) :=
  rfl

/-- The deformation category `Def_{P₂}` of the second section ring. -/
abbrev deformationCategory_ring₂ (c : TwoAffineOpenCover X)
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier)) :=
  let P : CommAlgCat k := hX.sectionsAlgOverSpec c.U₂
  FlatAlgebraCat.deformationCategory Λ k P

/-- `deformationCategory_ring₂` is the Over-slice at the residue object `(k, P₂)`. -/
theorem deformationCategory_ring₂_spec (c : TwoAffineOpenCover X)
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier)) :
    deformationCategory_ring₂ Λ k c hX =
      (let P : CommAlgCat k := hX.sectionsAlgOverSpec c.U₂
       Over (Fiber.fiberInclusion.obj (FlatAlgebraCat.residueObj Λ k P))) :=
  rfl

/-- The deformation category `Def_{P₁₂}` of the overlap section ring. -/
abbrev deformationCategory_ringInf (c : TwoAffineOpenCover X)
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier)) :=
  let P : CommAlgCat k := hX.sectionsAlgOverSpec (c.U₁ ⊓ c.U₂)
  FlatAlgebraCat.deformationCategory Λ k P

/-- `deformationCategory_ringInf` is the Over-slice at the residue object `(k, P₁₂)`. -/
theorem deformationCategory_ringInf_spec (c : TwoAffineOpenCover X)
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier)) :
    deformationCategory_ringInf Λ k c hX =
      (let P : CommAlgCat k := hX.sectionsAlgOverSpec (c.U₁ ⊓ c.U₂)
       Over (Fiber.fiberInclusion.obj (FlatAlgebraCat.residueObj Λ k P))) :=
  rfl

end AlgebraicGeometry.Scheme.TwoAffineOpenCover
