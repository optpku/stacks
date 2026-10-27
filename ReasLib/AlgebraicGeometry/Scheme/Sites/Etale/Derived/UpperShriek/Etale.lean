/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.UpperShriek.Comparison

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

section ExtensionByZero

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] [LocallyQuasiFinite j]
variable (Λ : Type u) [CommRing Λ]
variable [U.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction j).op]
variable [LocallyOfFiniteType j]
variable [HasWeakSheafify U.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ V : U.Etale,
  HasWeakSheafify (U.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [∀ V : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero j (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero j (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero j (ModuleCat.{u} Λ))]
variable [(etaleRestrictionSheaf j (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleRestrictionSheaf j (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits (etaleRestrictionSheaf j (ModuleCat.{u} Λ))]
variable [IsGrothendieckAbelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Derived module upper shriek along an étale morphism is naturally
isomorphic to derived restriction, by uniqueness of right adjoints. -/
def upperShriekModuleDerivedIsoRestriction :
    upperShriekModuleDerived j Λ ≅ etaleDerivedRestriction j Λ :=
  conjugateIsoEquiv (lowerShriekModuleDerivedAdjunction j Λ)
    (etaleDerivedExtensionByZeroAdjunction j Λ)
    (lowerShriekModuleDerivedIsoExtensionByZero j Λ).symm

/-- The component of the derived upper-shriek identification at a derived module sheaf. -/
def upperShriekModuleDerivedIsoRestriction_app
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (upperShriekModuleDerived j Λ).obj K ≅ (etaleDerivedRestriction j Λ).obj K :=
  (upperShriekModuleDerivedIsoRestriction j Λ).app K

end ExtensionByZero

variable {Y : Scheme.{u}} (X : Over Y) (Λ : Type u) [CommRing Λ]
variable [IsSeparated X.hom] [Etale X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (P : Compactification.Of Y X)
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [X.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [P.obj.right.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [P.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Compactification.Of.ι P)).op]
variable [IsGrothendieckAbelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction X.hom).op.HasLeftKanExtension F]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction X.hom).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero X.hom (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero X.hom (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero X.hom (ModuleCat.{u} Λ))]
variable [(etaleRestrictionSheaf X.hom (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleRestrictionSheaf X.hom (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits (etaleRestrictionSheaf X.hom (ModuleCat.{u} Λ))]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction X.hom).op]

variable [Fact (AddMonoid.IsTorsion Λ)]

/-- For a separated étale morphism between quasi-compact quasi-separated
schemes and torsion coefficients, compactification-derived upper shriek is
naturally isomorphic to derived restriction. -/
def etaleDerivedUpperShriekIsoRestriction :
    etaleDerivedUpperShriek X Λ P ≅ etaleDerivedRestriction X.hom Λ :=
  etaleDerivedUpperShriekIso X Λ P ≪≫ upperShriekModuleDerivedIsoRestriction X.hom Λ

/-- The component of the compactification-derived upper-shriek identification. -/
def etaleDerivedUpperShriekIsoRestriction_app
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (etaleDerivedUpperShriek X Λ P).obj K ≅ (etaleDerivedRestriction X.hom Λ).obj K :=
  (etaleDerivedUpperShriekIsoRestriction X Λ P).app K

/-- The derived upper-shriek identification is the mate of the inverse
lower-shriek identification under the two derived adjunctions. -/
theorem etaleDerivedUpperShriekIsoRestriction_spec :
    etaleDerivedUpperShriekIsoRestriction X Λ P =
      conjugateIsoEquiv (etaleDerivedLowerShriekAdjunction X Λ P)
        (etaleDerivedExtensionByZeroAdjunction X.hom Λ)
        (etaleDerivedLowerShriekIsoExtensionByZero X Λ P).symm := sorry

end AlgebraicGeometry.Scheme.Etale

end
