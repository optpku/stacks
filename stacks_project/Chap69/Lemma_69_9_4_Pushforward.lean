/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Derived.ClosedImmersion

/-! # Derived small-étale pushforward along a closed immersion -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

-- Local instance justification (defeq pin): sheaf preadditive inference otherwise differs from the Abelian-induced structures fixed by DerivedCategory.Qh and exact-derived factorization; pin the existing canonical projections consistently for homotopy categories, additive binders, and derived models.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

variable {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
variable [Etale (closedImmersionComplementι i)]
variable [Abelian (EtaleSheaf X)] [Abelian (EtaleSheaf Z)]
variable [Abelian (EtaleSheaf (closedImmersionComplement i))]
variable [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology Z) AddCommGrpCat.{u + 1}]
variable [HasDerivedCategory (EtaleSheaf X)] [HasDerivedCategory (EtaleSheaf Z)]

variable [(sheafPushforward AddCommGrpCat.{u + 1} i).Additive]
variable [(sheafInverseImage AddCommGrpCat.{u + 1} i).Additive]

#check (AlgebraicGeometry.AlgebraicSpace.etaleDerivedDirectImage.toSupported i :
  EtaleDerived Z ⥤ EtaleDerivedSupported i)

#check (AlgebraicGeometry.AlgebraicSpace.etaleDerivedDirectImage_rightDerivedModel i :
  EtaleRightDerivedModel (sheafPushforward AddCommGrpCat.{u + 1} i))
