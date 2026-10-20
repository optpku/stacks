/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import ReasLib.Algebra.Homology.DerivedCategory.Adjunction
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero

/-!
# Derived extension by zero along étale open immersions

This module promotes the exact sheaf-level functors `j⁻¹` and `j_!` on the small
étale site to unbounded derived categories, and records the adjunction and
composition isomorphisms along open inclusions.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Etale

/-- The abelian structure supplies the canonical preadditive structure on sheaves
of `Λ`-modules on the small étale site. -/
instance etaleModuleSheaf_preadditive
    (Y : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    [Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))] :
    Preadditive (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) :=
  (inferInstance : Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))).toPreadditive

section DerivedFunctors

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
variable (Λ : Type v) [CommRing Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ V : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over V) (ModuleCat.{v} Λ)]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasWeakSheafify U.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ V : U.Etale,
  HasWeakSheafify (U.smallEtaleTopology.over V) (ModuleCat.{v} Λ)]
variable [Abelian (Sheaf U.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [(etaleRestrictionSheaf j (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (etaleRestrictionSheaf j (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (etaleRestrictionSheaf j (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero j (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero j (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero j (ModuleCat.{v} Λ))]

/-- Derived restriction `j⁻¹ : D(X_étale, Λ) ⥤ D(U_étale, Λ)` along an étale
morphism, induced by the exact sheaf restriction functor. -/
noncomputable abbrev etaleDerivedRestriction :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤ DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{v} Λ)) :=
  (etaleRestrictionSheaf j (ModuleCat.{v} Λ)).mapDerivedCategory

/-- Derived étale restriction is `mapDerivedCategory` of sheaf restriction. -/
theorem etaleDerivedRestriction_def :
    etaleDerivedRestriction j Λ =
      (etaleRestrictionSheaf j (ModuleCat.{v} Λ)).mapDerivedCategory :=
  sorry

/-- Derived extension by zero `j_! : D(U_étale, Λ) ⥤ D(X_étale, Λ)` along an étale
morphism, induced by the exact sheaf-level functor `moduleExtensionByZero`. -/
noncomputable abbrev etaleDerivedExtensionByZero :
    DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤ DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) :=
  (etaleExtensionByZero j (ModuleCat.{v} Λ)).mapDerivedCategory

/-- Derived étale extension by zero is `mapDerivedCategory` of
`moduleExtensionByZero`. -/
theorem etaleDerivedExtensionByZero_def :
    etaleDerivedExtensionByZero j Λ =
      (etaleExtensionByZero j (ModuleCat.{v} Λ)).mapDerivedCategory :=
  sorry

/-- The adjunction `j_! ⊣ j⁻¹` on unbounded derived categories of étale
`Λ`-modules. -/
noncomputable def etaleDerivedExtensionByZeroAdjunction :
    etaleDerivedExtensionByZero j Λ ⊣ etaleDerivedRestriction j Λ :=
  Adjunction.mapDerivedCategory (etaleExtensionByZero_adjunction j (ModuleCat.{v} Λ))

/-- The composite `j_!((-) |_U)` on `D(X_étale, Λ)`. -/
noncomputable abbrev etaleDerivedExtensionByZeroRestrict :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) ⥤ DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) :=
  etaleDerivedRestriction j Λ ⋙ etaleDerivedExtensionByZero j Λ

/-- The composite `j_!((-) |_U)` evaluates as extension by zero of the
restricted object. -/
theorem etaleDerivedExtensionByZeroRestrict_obj (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))) :
    (etaleDerivedExtensionByZeroRestrict j Λ).obj K =
      (etaleDerivedExtensionByZero j Λ).obj
        ((etaleDerivedRestriction j Λ).obj K) :=
  sorry

end DerivedFunctors

section OpenInclusion

variable {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V)
variable (Λ : Type v) [CommRing Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ W : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over W) (ModuleCat.{v} Λ)]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasWeakSheafify V.toScheme.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ W : V.toScheme.Etale,
  HasWeakSheafify (V.toScheme.smallEtaleTopology.over W) (ModuleCat.{v} Λ)]
variable [Abelian (Sheaf V.toScheme.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory
  (Sheaf V.toScheme.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasWeakSheafify U.toScheme.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ W : U.toScheme.Etale,
  HasWeakSheafify (U.toScheme.smallEtaleTopology.over W) (ModuleCat.{v} Λ)]
variable [Abelian (Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory
  (Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [∀ F : U.toScheme.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
  (etaleRestriction (U.ι)).op.HasLeftKanExtension F]
variable [∀ F : V.toScheme.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
  (etaleRestriction (V.ι)).op.HasLeftKanExtension F]
variable [∀ F : U.toScheme.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
  (etaleRestriction ((X.homOfLE h))).op.HasLeftKanExtension F]
variable [(etaleRestrictionSheaf (U.ι) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (etaleRestrictionSheaf (U.ι) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (etaleRestrictionSheaf (U.ι) (ModuleCat.{v} Λ))]
variable [(etaleRestrictionSheaf (V.ι) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (etaleRestrictionSheaf (V.ι) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (etaleRestrictionSheaf (V.ι) (ModuleCat.{v} Λ))]
variable [(etaleRestrictionSheaf ((X.homOfLE h)) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleRestrictionSheaf ((X.homOfLE h)) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits
  (etaleRestrictionSheaf ((X.homOfLE h)) (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero (U.ι) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero (U.ι) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero (U.ι) (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero (V.ι) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero (V.ι) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero (V.ι) (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero ((X.homOfLE h)) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero ((X.homOfLE h)) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero ((X.homOfLE h)) (ModuleCat.{v} Λ))]
variable [(etaleRestrictionSheaf (V.ι) (ModuleCat.{v} Λ) ⋙
    etaleRestrictionSheaf ((X.homOfLE h)) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleRestrictionSheaf (V.ι) (ModuleCat.{v} Λ) ⋙
    etaleRestrictionSheaf ((X.homOfLE h)) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits
  (etaleRestrictionSheaf (V.ι) (ModuleCat.{v} Λ) ⋙
    etaleRestrictionSheaf ((X.homOfLE h)) (ModuleCat.{v} Λ))]
variable [(etaleExtensionByZero ((X.homOfLE h)) (ModuleCat.{v} Λ) ⋙
    etaleExtensionByZero (V.ι) (ModuleCat.{v} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero ((X.homOfLE h)) (ModuleCat.{v} Λ) ⋙ etaleExtensionByZero (V.ι) (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero ((X.homOfLE h)) (ModuleCat.{v} Λ) ⋙ etaleExtensionByZero (V.ι) (ModuleCat.{v} Λ))]

/-- Site-level identification of étale restriction along `U.ι` with restriction
along `V.ι` followed by restriction along `X.homOfLE h`. -/
noncomputable def etaleRestriction_comp :
    etaleRestriction ((X.homOfLE h)) ⋙ etaleRestriction (V.ι) ≅
      etaleRestriction (U.ι) :=
  (MorphismProperty.Over.mapComp (⊤ : MorphismProperty Scheme)
      (inferInstance : Etale (X.homOfLE h))
      (inferInstance : Etale (V.ι)) (U.ι) (Scheme.homOfLE_ι X h).symm).symm

/-- Sheaf-level identification of restriction to `U` with restriction to `V`
followed by restriction along `X.homOfLE h`. -/
noncomputable def etaleRestrictionSheaf_comp :
    etaleRestrictionSheaf (V.ι) (ModuleCat.{v} Λ) ⋙
        etaleRestrictionSheaf ((X.homOfLE h)) (ModuleCat.{v} Λ) ≅
      etaleRestrictionSheaf (U.ι) (ModuleCat.{v} Λ) :=
  Functor.sheafPushforwardContinuousComp' (etaleRestriction_comp h)
    (ModuleCat.{v} Λ) U.toScheme.smallEtaleTopology V.toScheme.smallEtaleTopology
    X.smallEtaleTopology

/-- Sheaf-level identification of extension by zero from `U` with extension by
zero along `X.homOfLE h` followed by extension by zero from `V`. -/
noncomputable def moduleExtensionByZero_comp :
    etaleExtensionByZero ((X.homOfLE h)) (ModuleCat.{v} Λ) ⋙ etaleExtensionByZero (V.ι) (ModuleCat.{v} Λ) ≅
      etaleExtensionByZero (U.ι) (ModuleCat.{v} Λ) :=
  Adjunction.leftAdjointCompIso
    (etaleExtensionByZero_adjunction (X.homOfLE h) (ModuleCat.{v} Λ))
    (etaleExtensionByZero_adjunction (V.ι) (ModuleCat.{v} Λ))
    (etaleExtensionByZero_adjunction (U.ι) (ModuleCat.{v} Λ))
    (etaleRestrictionSheaf_comp h Λ)

/-- Derived restriction to `U` identifies with restriction to `V` followed by
restriction along `X.homOfLE h`. -/
noncomputable def etaleDerivedRestriction_comp :
    etaleDerivedRestriction (U.ι) Λ ≅
      etaleDerivedRestriction (V.ι) Λ ⋙
        etaleDerivedRestriction ((X.homOfLE h)) Λ :=
  Functor.MapDerivedCategory.functorIso
      (etaleRestrictionSheaf_comp h Λ).symm ≪≫
    ExactFunctor.MapDerivedCategory.compFunctorIso
      (ExactFunctor.of (etaleRestrictionSheaf (V.ι) (ModuleCat.{v} Λ)))
      (ExactFunctor.of (etaleRestrictionSheaf ((X.homOfLE h)) (ModuleCat.{v} Λ)))

/-- Derived extension by zero from `U` identifies with extension by zero along
`X.homOfLE h` followed by extension by zero from `V`. -/
noncomputable def etaleDerivedExtensionByZero_comp :
    etaleDerivedExtensionByZero ((X.homOfLE h)) Λ ⋙
        etaleDerivedExtensionByZero (V.ι) Λ ≅
      etaleDerivedExtensionByZero (U.ι) Λ :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
      (ExactFunctor.of (etaleExtensionByZero ((X.homOfLE h)) (ModuleCat.{v} Λ)))
      (ExactFunctor.of (etaleExtensionByZero (V.ι) (ModuleCat.{v} Λ)))).symm ≪≫
    Functor.MapDerivedCategory.functorIso (moduleExtensionByZero_comp h Λ)

end OpenInclusion

end AlgebraicGeometry.Scheme.Etale

end
