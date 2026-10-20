/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Derived.Supported

/-! # Étale derived categories supported on a closed subspace -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

-- Local instance justification (defeq pin): sheaf preadditive inference otherwise differs from the Abelian-induced structures fixed by DerivedCategory.Qh and exact-derived factorization; pin the existing canonical projections consistently for homotopy categories, additive binders, and derived models.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace

-- These specialized compatibility registrations keep the preadditive and zero-morphism
-- structures definitionally equal to those used by the derived-category API. Importers
-- such as the derived étale stalk API need the same selection for additivity inference.

/-- Abelian étale sheaves carry the preadditive structure of their abelian category. -/
instance (priority := 2000) etaleSheaf_preadditive {S : Scheme.{u}}
    (X : AlgebraicSpace S) [Abelian (EtaleSheaf X)] : Preadditive (EtaleSheaf X) :=
  Abelian.toPreadditive

/-- Zero morphisms of abelian étale sheaves are the zero elements of their hom groups. -/
instance (priority := 2000) etaleSheaf_hasZeroMorphisms {S : Scheme.{u}}
    (X : AlgebraicSpace S) [Abelian (EtaleSheaf X)] : HasZeroMorphisms (EtaleSheaf X) :=
  Preadditive.preadditiveHasZeroMorphisms

end AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
variable [Etale (closedImmersionComplementι i)]
variable [Abelian (EtaleSheaf X)] [Abelian (EtaleSheaf Z)]
variable [Abelian (EtaleSheaf (closedImmersionComplement i))]
variable [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology Z) AddCommGrpCat.{u + 1}]
variable [HasDerivedCategory (EtaleSheaf X)] [HasDerivedCategory (EtaleSheaf Z)]

#check (AlgebraicGeometry.AlgebraicSpace.etaleDerivedSupportedOn_mem_iff i :
  ∀ K : EtaleDerived X,
    etaleDerivedSupportedOn i K ↔
      ∀ n : ℤ, etaleSheafSupportedOn i
        ((DerivedCategory.homologyFunctor (EtaleSheaf X) n).obj K))

#check (AlgebraicGeometry.AlgebraicSpace.EtaleDerivedSupported.inclusion i :
  EtaleDerivedSupported i ⥤ EtaleDerived X)
