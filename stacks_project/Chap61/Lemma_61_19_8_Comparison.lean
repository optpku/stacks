/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Abelian
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import stacks_project.Chap61.Lemma_61_19_1_Comparison

/-!
# Derived étale-to-pro-étale comparison for sheaves of modules

The essential image of `ε⁻¹` on sheaves of `Λ`-modules, together with the
bounded-below derived adjunction `ε⁻¹ ⊣ Rε_*` and its lift to
`D⁺_C(X.ProEt, Λ)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]

/-- Direct image of sheaves of `Λ`-modules along `etaleToProEt` is additive. -/
instance etaleToProEtSheaf_module_additive :
    (etaleToProEtSheaf X (ModuleCat.{u + 1} Λ)).Additive :=
  sorry

/-- The bounded-below right-derived functor of `Λ`-module `ε_*` exists. -/
instance etaleToProEtSheaf_module_hasRightDerivedFunctor :
    (etaleToProEtSheaf X (ModuleCat.{u + 1} Λ)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))) :=
  sorry

/-- Bounded-below derived direct image `Rε_*` on sheaves of `Λ`-modules. -/
def etaleToProEt_modulePlusPushforward :
    DerivedCategory.Plus (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  Adjunction.Derived.Plus.right (etaleToProEtSheaf X (ModuleCat.{u + 1} Λ))

variable [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
    (etaleToProEt X).op.HasLeftKanExtension F]

/-- The essential image of `ε⁻¹` on sheaves of `Λ`-modules along `etaleToProEt`. -/
abbrev etaleToProEtModuleEssImage :
    ObjectProperty (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
  Functor.essImage (etaleToProEtPullback X (ModuleCat.{u + 1} Λ))

/-- Membership in the essential image of `Λ`-module `ε⁻¹` is detected by the
sheaf-level adjunction counit. -/
theorem etaleToProEtModuleEssImage_iff_counit_isIso
    (G : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    etaleToProEtModuleEssImage X Λ G ↔
      IsIso ((etaleToProEt_sheafAdjunction X (ModuleCat.{u + 1} Λ)).counit.app G) :=
  sorry

/-- Restriction of derived direct image `Rε_*` to `D⁺` objects with cohomology in
`etaleToProEtModuleEssImage`. -/
def etaleToProEt_modulePlusPushforwardRestrict :
    DerivedCategory.Plus.CohomologyIn (etaleToProEtModuleEssImage X Λ) ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (DerivedCategory.Plus.cohomologyIn (etaleToProEtModuleEssImage X Λ)).ι ⋙
    etaleToProEt_modulePlusPushforward X Λ

/-- The sheaf-level adjunction unit of `Λ`-module `ε⁻¹ ⊣ ε_*` is an isomorphism. -/
instance etaleToProEt_sheafAdjunction_module_unit_app_isIso
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((etaleToProEt_sheafAdjunction X (ModuleCat.{u + 1} Λ)).unit.app F) :=
  sorry

variable [PreservesFiniteLimits (etaleToProEtPullback X (ModuleCat.{u + 1} Λ))]
variable [PreservesFiniteColimits (etaleToProEtPullback X (ModuleCat.{u + 1} Λ))]

/-- Bounded-below derived inverse image `ε⁻¹` on sheaves of `Λ`-modules. -/
def etaleToProEt_modulePlusPullback :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
  Adjunction.Derived.Plus.left
    (ExactFunctor.of (etaleToProEtPullback X (ModuleCat.{u + 1} Λ)))

/-- Bounded-below derived adjunction `ε⁻¹ ⊣ Rε_*` on sheaves of `Λ`-modules. -/
def etaleToProEt_modulePlusAdjunction :
    etaleToProEt_modulePlusPullback X Λ ⊣ etaleToProEt_modulePlusPushforward X Λ :=
  Adjunction.Derived.Plus.adjunction
    (ExactFunctor.of (etaleToProEtPullback X (ModuleCat.{u + 1} Λ)))
    (etaleToProEtSheaf X (ModuleCat.{u + 1} Λ))
    (etaleToProEt_sheafAdjunction X (ModuleCat.{u + 1} Λ))

/-- Derived inverse image `ε⁻¹` sends every object of `D⁺(X.Etale, Λ)` into
`D⁺` objects whose cohomology lies in `etaleToProEtModuleEssImage`. -/
theorem etaleToProEt_modulePlusPullback_mapsTo
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    DerivedCategory.Plus.cohomologyIn (etaleToProEtModuleEssImage X Λ)
      ((etaleToProEt_modulePlusPullback X Λ).obj K) :=
  sorry

/-- The lift of derived inverse image `ε⁻¹` through `D⁺_C(X.ProEt, Λ)`. -/
def etaleToProEt_modulePlusPullbackLift :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus.CohomologyIn (etaleToProEtModuleEssImage X Λ) :=
  (DerivedCategory.Plus.cohomologyIn (etaleToProEtModuleEssImage X Λ)).lift
    (etaleToProEt_modulePlusPullback X Λ) (etaleToProEt_modulePlusPullback_mapsTo X Λ)

/-- The lift of derived inverse image `ε⁻¹` recovers `etaleToProEt_modulePlusPullback`
after inclusion of `D⁺_C`. -/
def etaleToProEt_modulePlusPullbackLift_compι :
    etaleToProEt_modulePlusPullbackLift X Λ ⋙
      (DerivedCategory.Plus.cohomologyIn (etaleToProEtModuleEssImage X Λ)).ι ≅
        etaleToProEt_modulePlusPullback X Λ :=
  (DerivedCategory.Plus.cohomologyIn (etaleToProEtModuleEssImage X Λ)).liftCompιIso
    (etaleToProEt_modulePlusPullback X Λ) (etaleToProEt_modulePlusPullback_mapsTo X Λ)

end AlgebraicGeometry.Scheme

end

end
