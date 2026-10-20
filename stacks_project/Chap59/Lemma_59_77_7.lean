/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ConstantFiniteProjective
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open AlgebraicGeometry
open DerivedCategory.TStructure

universe u v

/- Lemma 59.77.7: a connected scheme admits one finite-projective constant complex
on an étale covering for a constructible Tor-finite derived object with locally constant
cohomology. -/
@[stacks 09BI] #check
  (AlgebraicGeometry.Scheme.exists_finiteProjective_constant_model :
    ∀ {X : Scheme.{u}} [ConnectedSpace X] {Λ : Type v} [CommRing Λ] [IsNoetherianRing Λ]
      [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{v} Λ)]
      [∀ (Y : Scheme.{u}) (U : Y.Etale),
        HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
      [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z) (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ),
        (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
      [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
      [∀ U : X.Etale, Abelian (Sheaf (X.smallEtaleTopology.over U) (ModuleCat.{v} Λ))]
      [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
      [∀ U : X.Etale,
        HasDerivedCategory (Sheaf (X.smallEtaleTopology.over U) (ModuleCat.{v} Λ))]
      [∀ U : X.Etale,
        ((X.smallEtaleTopology.over U).W (A := ModuleCat.{v} Λ)).IsMonoidal]
      [∀ U : X.Etale, (X.smallEtaleTopology.overPullback (ModuleCat.{v} Λ) U).Additive]
      [∀ U : X.Etale,
        PreservesFiniteLimits (X.smallEtaleTopology.overPullback (ModuleCat.{v} Λ) U)]
      [∀ U : X.Etale,
        PreservesFiniteColimits (X.smallEtaleTopology.overPullback (ModuleCat.{v} Λ) U)]
      (K : Scheme.Etale.Derived.ConstructibleTorFinite X Λ)
      (hKbounded :
        (t.bounded : ObjectProperty
          (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))) K.obj)
      (hKcohomology :
        DerivedCategory.cohomologyIn
          (CategoryTheory.Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ)
          K.obj),
      ∃ M : CochainComplex (ModuleCat.{v} Λ) ℤ,
        M.IsBoundedFiniteProjective ∧
          ∃ T : X.smallEtaleTopology.Cover (⊤_ X.Etale),
            ∀ I : T.Arrow,
              Nonempty
                (DerivedRestriction.obj K.obj I.Y ≅
                  DerivedRestriction.ofComplex
                    (DerivedRestriction.restrictConstantComplex M I.Y)))
