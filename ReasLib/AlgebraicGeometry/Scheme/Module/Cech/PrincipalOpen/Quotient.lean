/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Linear
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.Derived

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape TopologicalSpace

noncomputable section

universe u

namespace ModuleCech.LocalCohomology

variable {X : Scheme.{u}}

/-- The finite-family multiplication map `(f_i) : ℱ^⊕c ⟶ ℱ`. -/
noncomputable def sectionMultiplication {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (ℱ : X.Modules) :
    (Scheme.Modules.toRingedSpace X).obj (⨁ (fun _ : Fin c ↦ ℱ)) ⟶
      (Scheme.Modules.toRingedSpace X).obj ℱ :=
  (Scheme.Modules.toRingedSpace X).map
    (biproduct.desc fun i ↦ RingedSpace.globalSectionMul (f i) ℱ)

/-- A module morphism acts diagonally on a finite direct sum. -/
noncomputable def sectionSumMap {c : ℕ} {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    (Scheme.Modules.toRingedSpace X).obj (⨁ (fun _ : Fin c ↦ ℱ)) ⟶
      (Scheme.Modules.toRingedSpace X).obj (⨁ (fun _ : Fin c ↦ 𝒢)) :=
  (Scheme.Modules.toRingedSpace X).map
    (biproduct.lift fun i ↦ biproduct.π (fun _ : Fin c ↦ ℱ) i ≫ φ)

/-- Finite-family multiplication is natural in the module sheaf. -/
theorem sectionMultiplication_naturality {c : ℕ} (f : Fin c → Γ(X, ⊤))
    {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    sectionMultiplication f ℱ ≫ (Scheme.Modules.toRingedSpace X).map φ =
      sectionSumMap φ ≫ sectionMultiplication f 𝒢 := sorry

/-- The map on finite-family quotients induced by a module morphism. -/
noncomputable def quotientMap {c : ℕ} (f : Fin c → Γ(X, ⊤))
    {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    cokernel (sectionMultiplication f ℱ) ⟶ cokernel (sectionMultiplication f 𝒢) :=
  cokernel.map (sectionMultiplication f ℱ) (sectionMultiplication f 𝒢)
    (sectionSumMap φ) ((Scheme.Modules.toRingedSpace X).map φ)
    (sectionMultiplication_naturality f φ)

/-- The finite-family quotient map preserves identities. -/
theorem quotientMap_id {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    quotientMap f (𝟙 ℱ) = 𝟙 (cokernel (sectionMultiplication f ℱ)) := sorry

/-- The finite-family quotient map preserves composition. -/
theorem quotientMap_comp {c : ℕ} (f : Fin c → Γ(X, ⊤))
    {ℱ 𝒢 ℋ : X.Modules} (φ : ℱ ⟶ 𝒢) (ψ : 𝒢 ⟶ ℋ) :
    quotientMap f (φ ≫ ψ) = quotientMap f φ ≫ quotientMap f ψ := sorry

/-- The functorial cokernel of `(f_i) : ℱ^⊕c ⟶ ℱ`, representing `i_*i^*ℱ`. -/
noncomputable def quotientFunctor {c : ℕ} (f : Fin c → Γ(X, ⊤)) :
    X.Modules ⥤ X.toRingedSpace.Modules where
  obj ℱ := cokernel (sectionMultiplication f ℱ)
  map φ := quotientMap f φ
  map_id ℱ := quotientMap_id f ℱ
  map_comp φ ψ := quotientMap_comp f φ ψ

/-- Evaluation of the finite-family quotient functor is the displayed cokernel. -/
theorem quotientFunctor_obj {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    (quotientFunctor f).obj ℱ = cokernel (sectionMultiplication f ℱ) := sorry

/-- Naturality of the canonical projection to the finite-family quotient. -/
theorem quotientProjection_naturality {c : ℕ} (f : Fin c → Γ(X, ⊤))
    {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) :
    (Scheme.Modules.toRingedSpace X).map φ ≫
        cokernel.π (sectionMultiplication f 𝒢) =
      cokernel.π (sectionMultiplication f ℱ) ≫ quotientMap f φ := sorry

/-- The canonical projection from a module sheaf to its finite-family quotient. -/
noncomputable def quotientProjection {c : ℕ} (f : Fin c → Γ(X, ⊤)) :
    Scheme.Modules.toRingedSpace X ⟶ quotientFunctor f where
  app ℱ := cokernel.π (sectionMultiplication f ℱ)
  naturality _ _ φ := quotientProjection_naturality f φ

/-- Restriction of a module sheaf to the common zero locus. -/
noncomputable def pullbackFunctor {c : ℕ} (f : Fin c → Γ(X, ⊤)) :
    X.Modules ⥤ SheafOfModules.ClosedSubset.Modules
      X.toRingedSpace.ringCatSheaf (ModuleCech.ofSectionsZeroLocus f) :=
  Scheme.Modules.toRingedSpace X ⋙ SheafOfModules.ClosedSubset.pullback
    X.toRingedSpace.ringCatSheaf (ModuleCech.ofSectionsZeroLocus f)

/-- Evaluation of `pullbackFunctor` is direct restriction to the common zero locus. -/
theorem pullbackFunctor_obj {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    (pullbackFunctor f).obj ℱ =
      (SheafOfModules.ClosedSubset.pullback X.toRingedSpace.ringCatSheaf
        (ModuleCech.ofSectionsZeroLocus f)).obj
        ((Scheme.Modules.toRingedSpace X).obj ℱ) := sorry

/-- Restriction of the finite-family quotient to the common zero locus. -/
noncomputable def zeroLocusPullback {c : ℕ} (f : Fin c → Γ(X, ⊤)) :
    X.Modules ⥤ SheafOfModules.ClosedSubset.Modules
      X.toRingedSpace.ringCatSheaf (ModuleCech.ofSectionsZeroLocus f) :=
  quotientFunctor f ⋙ SheafOfModules.ClosedSubset.pullback
    X.toRingedSpace.ringCatSheaf (ModuleCech.ofSectionsZeroLocus f)

/-- Evaluation of `zeroLocusPullback` is restriction of the finite-family cokernel. -/
theorem zeroLocusPullback_obj {c : ℕ} (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    (zeroLocusPullback f).obj ℱ =
      (SheafOfModules.ClosedSubset.pullback X.toRingedSpace.ringCatSheaf
        (ModuleCech.ofSectionsZeroLocus f)).obj
        (cokernel (sectionMultiplication f ℱ)) := sorry

/-- Restriction of the canonical projection to the finite-family quotient. -/
noncomputable def pullbackQuotientProjection {c : ℕ} (f : Fin c → Γ(X, ⊤)) :
    pullbackFunctor f ⟶ zeroLocusPullback f :=
  Functor.whiskerRight (quotientProjection f)
    (SheafOfModules.ClosedSubset.pullback X.toRingedSpace.ringCatSheaf
      (ModuleCech.ofSectionsZeroLocus f))

/-- On each module sheaf, `pullbackQuotientProjection` is the pullback of the cokernel
projection. -/
theorem pullbackQuotientProjection_app {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    (pullbackQuotientProjection f).app ℱ =
      (SheafOfModules.ClosedSubset.pullback X.toRingedSpace.ringCatSheaf
        (ModuleCech.ofSectionsZeroLocus f)).map ((quotientProjection f).app ℱ) := sorry

/-- The finite-family quotient is supported on the common zero locus, so the unit from it to the
pushforward of its restriction is invertible. -/
noncomputable instance quotientUnitIsIso {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (ℱ : X.Modules) :
    IsIso ((SheafOfModules.pullbackPushforwardAdjunction
      (SheafOfModules.ClosedSubset.structureMap X.toRingedSpace.ringCatSheaf
        (ModuleCech.ofSectionsZeroLocus f))).unit.app ((quotientFunctor f).obj ℱ)) := sorry

/-- Pushing forward the restricted finite-family quotient canonically recovers the cokernel of
`(f_i) : ℱ^⊕c ⟶ ℱ`. -/
noncomputable def zeroLocusPullback_pushforwardIso {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    (SheafOfModules.ClosedSubset.pushforward X.toRingedSpace.ringCatSheaf
        (ModuleCech.ofSectionsZeroLocus f)).obj ((zeroLocusPullback f).obj ℱ) ≅
      (quotientFunctor f).obj ℱ :=
  (asIso ((SheafOfModules.pullbackPushforwardAdjunction
    (SheafOfModules.ClosedSubset.structureMap X.toRingedSpace.ringCatSheaf
      (ModuleCech.ofSectionsZeroLocus f))).unit.app ((quotientFunctor f).obj ℱ))).symm

/-- The inverse of `zeroLocusPullback_pushforwardIso` is the pullback-pushforward unit. -/
theorem zeroLocusPullback_pushforwardIso_inv {c : ℕ}
    (f : Fin c → Γ(X, ⊤)) (ℱ : X.Modules) :
    (zeroLocusPullback_pushforwardIso f ℱ).inv =
      (SheafOfModules.pullbackPushforwardAdjunction
        (SheafOfModules.ClosedSubset.structureMap X.toRingedSpace.ringCatSheaf
          (ModuleCech.ofSectionsZeroLocus f))).unit.app ((quotientFunctor f).obj ℱ) := sorry

end ModuleCech.LocalCohomology

end
