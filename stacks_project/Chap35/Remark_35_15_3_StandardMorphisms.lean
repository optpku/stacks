/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AffineScheme.StandardMorphisms

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.AffineScheme

#check (AlgebraicGeometry.AffineScheme.standardSmooth :
  MorphismProperty AffineScheme.{u})

#check (AlgebraicGeometry.AffineScheme.standardSyntomic :
  MorphismProperty AffineScheme.{u})

#check (AlgebraicGeometry.AffineScheme.standardEtale :
  MorphismProperty AffineScheme.{u})

#check (AlgebraicGeometry.AffineScheme.standardSmooth_iff :
  ∀ {X Y : AffineScheme.{u}} (f : X ⟶ Y),
    standardSmooth f ↔
      @StandardSmooth _ _ (forgetToScheme.map f)
        (AlgebraicGeometry.isAffine_affineScheme X)
        (AlgebraicGeometry.isAffine_affineScheme Y))

#check (AlgebraicGeometry.AffineScheme.standardSyntomic_iff :
  ∀ {X Y : AffineScheme.{u}} (f : X ⟶ Y),
    standardSyntomic f ↔
      @StandardSyntomic _ _ (forgetToScheme.map f)
        (AlgebraicGeometry.isAffine_affineScheme X)
        (AlgebraicGeometry.isAffine_affineScheme Y))

#check (AlgebraicGeometry.AffineScheme.standardEtale_iff :
  ∀ {X Y : AffineScheme.{u}} (f : X ⟶ Y),
    standardEtale f ↔
      @Algebra.IsStandardEtale
        (Scheme.Γ.obj (Opposite.op (forgetToScheme.obj Y)))
        (Scheme.Γ.obj (Opposite.op (forgetToScheme.obj X))) _ _
        (CommRingCat.Hom.hom (Scheme.Hom.appTop (forgetToScheme.map f))).toAlgebra)

#check (AlgebraicGeometry.AffineScheme.standardSmooth_le_smooth :
  standardSmooth.{u} ≤
    MorphismProperty.inverseImage (@Smooth : MorphismProperty Scheme.{u}) forgetToScheme)

#check (AlgebraicGeometry.AffineScheme.standardSyntomic_le_syntomic :
  standardSyntomic.{u} ≤
    MorphismProperty.inverseImage (@Syntomic : MorphismProperty Scheme.{u}) forgetToScheme)

#check (AlgebraicGeometry.AffineScheme.standardEtale_le_etale :
  standardEtale.{u} ≤
    MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u}) forgetToScheme)

end AlgebraicGeometry.AffineScheme
