/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.FractionClass
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Homology

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape TopologicalSpace

noncomputable section

universe u

namespace ModuleCech.LocalCohomology

variable {X : Scheme.{u}}

/-- The local-cohomology sheaf functor `ℱ ↦ H^c_Z(ℱ)` on the common zero locus. -/
noncomputable def cohomologyFunctor {c : ℕ} (f : Fin c → Γ(X, ⊤)) :
    X.Modules ⥤ SheafOfModules.ClosedSubset.Modules
      X.toRingedSpace.ringCatSheaf (ModuleCech.ofSectionsZeroLocus f) :=
  ModuleCech.moduleToDerived X ⋙
    SheafOfModules.ClosedSubset.Derived.sectionsWithSupport
      X.toRingedSpace.ringCatSheaf (ModuleCech.ofSectionsZeroLocus f) ⋙
    DerivedCategory.homologyFunctor
      (SheafOfModules.ClosedSubset.Modules X.toRingedSpace.ringCatSheaf
        (ModuleCech.ofSectionsZeroLocus f)) (c : ℤ)

/-- Evaluation of `cohomologyFunctor` is degree-`c` derived sections with support. -/
theorem cohomologyFunctor_obj {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    (cohomologyFunctor f).obj ℱ =
      (DerivedCategory.homologyFunctor
        (SheafOfModules.ClosedSubset.Modules X.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus f)) (c : ℤ)).obj
        ((SheafOfModules.ClosedSubset.Derived.sectionsWithSupport
          X.toRingedSpace.ringCatSheaf (ModuleCech.ofSectionsZeroLocus f)).obj
          ((ModuleCech.moduleToDerived X).obj ℱ)) := sorry

/-- Derived homology of the nonnegative Čech realization agrees with ordinary Čech homology. -/
noncomputable def cechDerivedHomologyIsoApp {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (ℱ : X.Modules) :
    (DerivedCategory.homologyFunctor X.toRingedSpace.Modules (c : ℤ)).obj
        ((ModuleCech.ofSectionsDerivedFunctor f).obj ℱ) ≅
      (cechCohomologyFunctor f).obj ℱ :=
  let K := ((Scheme.Modules.toRingedSpace X).mapHomologicalComplex (up ℕ)).obj
    (ModuleCech.ofSections f ℱ)
  (DerivedCategory.homologyFunctorFactors X.toRingedSpace.Modules (c : ℤ)).app
      (K.extend embeddingUpNat) ≪≫
    K.extendHomologyIso embeddingUpNat rfl

/-- The extension-by-zero homology comparison is natural in the coefficient module sheaf. -/
theorem cechDerivedHomologyIsoApp_naturality {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    (ModuleCech.ofSectionsDerivedFunctor f ⋙
        DerivedCategory.homologyFunctor X.toRingedSpace.Modules (c : ℤ)).map φ ≫
        (cechDerivedHomologyIsoApp f 𝒢).hom =
      (cechDerivedHomologyIsoApp f ℱ).hom ≫
        (cechCohomologyFunctor f).map φ := sorry

/-- The natural extension-by-zero comparison between derived and ordinary Čech homology. -/
noncomputable def cechDerivedHomologyIso {c : ℕ} (f : Fin c → Γ(X, ⊤)) :
    ModuleCech.ofSectionsDerivedFunctor f ⋙
        DerivedCategory.homologyFunctor X.toRingedSpace.Modules (c : ℤ) ≅
      cechCohomologyFunctor f :=
  NatIso.ofComponents (cechDerivedHomologyIsoApp f)
    (cechDerivedHomologyIsoApp_naturality f)

/-- The degree-`c` map induced by the derived Čech-to-local-cohomology comparison. -/
noncomputable def comparisonApp {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    (cechCohomologyFunctor f).obj ℱ ⟶
      ((cohomologyFunctor f ⋙ SheafOfModules.ClosedSubset.pushforward
        X.toRingedSpace.ringCatSheaf (ModuleCech.ofSectionsZeroLocus f)).obj ℱ) :=
  (cechDerivedHomologyIso f).inv.app ℱ ≫
    (DerivedCategory.homologyFunctor X.toRingedSpace.Modules (c : ℤ)).map
      ((ModuleCech.ofSectionsToLocalCohomology f).app ℱ) ≫
    (DerivedCategory.homologyFunctor X.toRingedSpace.Modules (c : ℤ)).map
      ((SheafOfModules.ClosedSubset.Derived.Pushforward.toSupportedCompιIso
        X.toRingedSpace.ringCatSheaf (ModuleCech.ofSectionsZeroLocus f)).hom.app
          ((SheafOfModules.ClosedSubset.Derived.sectionsWithSupport
            X.toRingedSpace.ringCatSheaf (ModuleCech.ofSectionsZeroLocus f)).obj
              ((ModuleCech.moduleToDerived X).obj ℱ))) ≫
    ((ExactFunctor.of (SheafOfModules.ClosedSubset.pushforward
      X.toRingedSpace.ringCatSheaf (ModuleCech.ofSectionsZeroLocus f))).homologyFunctorIso
        (c : ℤ)).hom.app
          ((SheafOfModules.ClosedSubset.Derived.sectionsWithSupport
            X.toRingedSpace.ringCatSheaf (ModuleCech.ofSectionsZeroLocus f)).obj
              ((ModuleCech.moduleToDerived X).obj ℱ))

/-- The degree-`c` comparison is natural in the coefficient module sheaf. -/
theorem comparison_naturality {c : ℕ} (f : Fin c → Γ(X, ⊤))
    {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    (cechCohomologyFunctor f).map φ ≫ comparisonApp f 𝒢 =
      comparisonApp f ℱ ≫
        (cohomologyFunctor f ⋙ SheafOfModules.ClosedSubset.pushforward
          X.toRingedSpace.ringCatSheaf
            (ModuleCech.ofSectionsZeroLocus f)).map φ := sorry

/-- The degree-`c` cohomology map induced by the derived comparison from the principal-open
Čech complex to supported local cohomology. -/
noncomputable def comparison {c : ℕ} (f : Fin c → Γ(X, ⊤)) :
    cechCohomologyFunctor f ⟶
      cohomologyFunctor f ⋙ SheafOfModules.ClosedSubset.pushforward
        X.toRingedSpace.ringCatSheaf (ModuleCech.ofSectionsZeroLocus f) where
  app ℱ := comparisonApp f ℱ
  naturality _ _ φ := comparison_naturality f φ

/-- Each component of `comparison` is the degree-`c` homology map induced by the derived
Čech-to-supported-cohomology comparison, followed by the canonical pushforward-homology
identification. -/
theorem comparison_app {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    (comparison f).app ℱ = comparisonApp f ℱ := sorry

/-- The quotient-presented map to `H^c_Z(ℱ)` attached to a finite family of global
sections. -/
noncomputable def quotientClassMap {c : ℕ} (f : Fin c → Γ(X, ⊤)) :
    zeroLocusPullback f ⟶ cohomologyFunctor f where
  app ℱ :=
    (SheafOfModules.ClosedSubset.pullback X.toRingedSpace.ringCatSheaf
      (ModuleCech.ofSectionsZeroLocus f)).map
        ((cechClass f).app ℱ ≫ (comparison f).app ℱ) ≫
      (SheafOfModules.pullbackPushforwardAdjunction
        (SheafOfModules.ClosedSubset.structureMap X.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus f))).counit.app ((cohomologyFunctor f).obj ℱ)
  naturality _ _ _ := sorry

/-- Naturality of the quotient-presented local-cohomology class map. -/
theorem quotientClassMap_naturality {c : ℕ} (f : Fin c → Γ(X, ⊤))
    {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    (zeroLocusPullback f).map φ ≫ (quotientClassMap f).app 𝒢 =
      (quotientClassMap f).app ℱ ≫ (cohomologyFunctor f).map φ := sorry

/-- After direct image, `quotientClassMap` is the cokernel-descended top Čech fraction class
followed by the degree-`c` derived Čech-to-supported-cohomology comparison. -/
theorem quotientClassMap_pushforward {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    (SheafOfModules.pullbackPushforwardAdjunction
        (SheafOfModules.ClosedSubset.structureMap X.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus f))).unit.app ((quotientFunctor f).obj ℱ) ≫
      (SheafOfModules.ClosedSubset.pushforward X.toRingedSpace.ringCatSheaf
        (ModuleCech.ofSectionsZeroLocus f)).map ((quotientClassMap f).app ℱ) =
    (cechClass f).app ℱ ≫ (comparison f).app ℱ := sorry

/-- The ambient restriction map to local cohomology obtained by composing the quotient
projection with `quotientClassMap`. -/
noncomputable def classMap {c : ℕ} (f : Fin c → Γ(X, ⊤)) :
    pullbackFunctor f ⟶ cohomologyFunctor f :=
  pullbackQuotientProjection f ≫ quotientClassMap f

/-- Naturality of the ambient-restriction local-cohomology class map. -/
theorem classMap_naturality {c : ℕ} (f : Fin c → Γ(X, ⊤))
    {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    (pullbackFunctor f).map φ ≫ (classMap f).app 𝒢 =
      (classMap f).app ℱ ≫ (cohomologyFunctor f).map φ := sorry

/-- After direct image, the ambient-restriction map is the quotient projection followed by the
top Čech fraction class and the degree-`c` derived Čech-to-supported-cohomology comparison. -/
theorem classMap_pushforward {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    (SheafOfModules.pullbackPushforwardAdjunction
        (SheafOfModules.ClosedSubset.structureMap X.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus f))).unit.app
            ((Scheme.Modules.toRingedSpace X).obj ℱ) ≫
      (SheafOfModules.ClosedSubset.pushforward X.toRingedSpace.ringCatSheaf
        (ModuleCech.ofSectionsZeroLocus f)).map ((classMap f).app ℱ) =
    (quotientProjection f).app ℱ ≫ (cechClass f).app ℱ ≫
      (comparison f).app ℱ := sorry

end ModuleCech.LocalCohomology

end
