/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Standard
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.StandardEtale

/-!
# Standard morphisms of affine schemes

This file packages standard smooth, standard syntomic, and standard étale morphisms as
morphism properties of the category of affine schemes.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.AffineScheme

/-- The morphism property of affine maps whose underlying scheme map is standard smooth. -/
def standardSmooth : MorphismProperty AffineScheme.{u} :=
  fun X Y f ↦
    @StandardSmooth _ _ (forgetToScheme.map f)
      (AlgebraicGeometry.isAffine_affineScheme X)
      (AlgebraicGeometry.isAffine_affineScheme Y)

/-- The morphism property of affine maps whose underlying scheme map is standard syntomic. -/
def standardSyntomic : MorphismProperty AffineScheme.{u} :=
  fun X Y f ↦
    @StandardSyntomic _ _ (forgetToScheme.map f)
      (AlgebraicGeometry.isAffine_affineScheme X)
      (AlgebraicGeometry.isAffine_affineScheme Y)

/-- The morphism property of affine maps whose global-sections algebra is standard étale. -/
def standardEtale : MorphismProperty AffineScheme.{u} :=
  fun _ _ f ↦
    @Algebra.IsStandardEtale
      (Scheme.Γ.obj (Opposite.op (forgetToScheme.obj _)))
      (Scheme.Γ.obj (Opposite.op (forgetToScheme.obj _))) _ _
      (CommRingCat.Hom.hom (Scheme.Hom.appTop (forgetToScheme.map f))).toAlgebra

/-- An affine morphism satisfies `standardSmooth` exactly when its underlying scheme map is
standard smooth. -/
theorem standardSmooth_iff {X Y : AffineScheme.{u}} (f : X ⟶ Y) :
    standardSmooth f ↔
      @StandardSmooth _ _ (forgetToScheme.map f)
        (AlgebraicGeometry.isAffine_affineScheme X)
        (AlgebraicGeometry.isAffine_affineScheme Y) := sorry

/-- An affine morphism satisfies `standardSyntomic` exactly when its underlying scheme map is
standard syntomic. -/
theorem standardSyntomic_iff {X Y : AffineScheme.{u}} (f : X ⟶ Y) :
    standardSyntomic f ↔
      @StandardSyntomic _ _ (forgetToScheme.map f)
        (AlgebraicGeometry.isAffine_affineScheme X)
        (AlgebraicGeometry.isAffine_affineScheme Y) := sorry

/-- An affine morphism satisfies `standardEtale` exactly when its global-sections algebra is
standard étale. -/
theorem standardEtale_iff {X Y : AffineScheme.{u}} (f : X ⟶ Y) :
    standardEtale f ↔
      @Algebra.IsStandardEtale
        (Scheme.Γ.obj (Opposite.op (forgetToScheme.obj Y)))
        (Scheme.Γ.obj (Opposite.op (forgetToScheme.obj X))) _ _
        (CommRingCat.Hom.hom (Scheme.Hom.appTop (forgetToScheme.map f))).toAlgebra := sorry

/-- A standard smooth affine morphism is smooth after forgetting to schemes. -/
theorem standardSmooth_le_smooth :
    standardSmooth.{u} ≤
      MorphismProperty.inverseImage (@Smooth : MorphismProperty Scheme.{u}) forgetToScheme := sorry

/-- A standard syntomic affine morphism is syntomic after forgetting to schemes. -/
theorem standardSyntomic_le_syntomic :
    standardSyntomic.{u} ≤
      MorphismProperty.inverseImage (@Syntomic : MorphismProperty Scheme.{u}) forgetToScheme := sorry

/-- A standard étale affine morphism is étale after forgetting to schemes. -/
theorem standardEtale_le_etale :
    standardEtale.{u} ≤
      MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u}) forgetToScheme := sorry

end AlgebraicGeometry.AffineScheme
