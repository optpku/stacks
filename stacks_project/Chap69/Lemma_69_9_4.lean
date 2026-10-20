/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Derived.ClosedImmersion
import StacksCheckRecall

/-! # Derived equivalence for a closed immersion of algebraic spaces -/

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

/- Lemma 69.9.4: exact small-étale pushforward identifies the derived category of the
closed subspace with the full subcategory supported on its image. The inverse is
restricted inverse image, naturally identified below with derived sections with support. -/
@[stacks 0AEI] #check
  (AlgebraicGeometry.AlgebraicSpace.etaleDerivedDirectImage.toSupported_isEquivalence i :
    (etaleDerivedDirectImage.toSupported i).IsEquivalence)

#check (AlgebraicGeometry.AlgebraicSpace.closedImmersion_etaleDerivedDirectImage_eq_underived i :
  ∀ closedModel : EtaleRightDerivedModel (sheafPushforward AddCommGrpCat.{u + 1} i),
    closedModel.functor ≅ etaleDerivedDirectImage i)

#check (AlgebraicGeometry.AlgebraicSpace.closedImmersion_etaleSupported_quasiInverse i :
  (etaleDerivedDirectImage.toSupported i).inv ≅ etaleDerivedSupported.inverseImage i)

#check (AlgebraicGeometry.AlgebraicSpace.closedImmersion_etaleSupported_quasiInverse_sections i :
  etaleDerivedSupported.inverseImage i ≅
    EtaleDerivedSupported.inclusion i ⋙ etaleDerivedSectionsWithSupport i)
