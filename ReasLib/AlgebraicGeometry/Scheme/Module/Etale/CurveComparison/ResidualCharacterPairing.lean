/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactResidualUnderlying
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.RelativeCohomologyUnderlying
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactHomologyPairing

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace AlgebraicGeometry.SchemeOverField.CompactResidual
variable {k : Type u} [Field k]
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (ηbar : GeometricPoint (geometricBaseChange X))

/-- Continuous character dual and geometric restriction commute through the identity
on actual continuous characters; equivariance uses φ(g⁻¹)=φ(g)⁻¹. -/
def characterRestrictionIso
    (K : CompactRepresentation.Cat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))) :
    (Ambient.restriction Λ X ηbar).obj
        (CompactRepresentation.continuousDual Λ
          (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar))) K) ≅
      CompactRepresentation.continuousDual Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar))
        ((restriction Λ X ηbar).obj K) :=
  { hom := ObjectProperty.homMk
      { hom := ModuleCat.ofHom
          { toFun := fun χ ↦ ⟨χ.val, χ.property⟩
            map_add' := sorry
            map_smul' := sorry }
        comm := fun _ ↦ sorry }
    inv := ObjectProperty.homMk
      { hom := ModuleCat.ofHom
          { toFun := fun χ ↦ ⟨χ.val, χ.property⟩
            map_add' := sorry
            map_smul' := sorry }
        comm := fun _ ↦ sorry }
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- The actual contragredient action on characters of a residual Galois module. -/
def characterGaloisAction (V : Action (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k)) :
    Action (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k) where
  V := ModuleCat.of Λ (CharacterModule V.V)
  ρ := { toFun := fun σ ↦ ModuleCat.ofHom (CharacterModule.dual (V.ρ σ⁻¹).hom)
         map_one' := sorry
         map_mul' := sorry }

/-- Kuhn's character comparison followed by the actual coefficient-restriction identity. -/
def residualCharacterIso
    (K : CompactRepresentation.Cat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))) (n : ℕ) :
    (CompactModule.forget Λ).obj
      ((CompactRepresentation.continuousHomology Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar)) n).obj
        ((restriction Λ X ηbar).obj K)) ≅
    ModuleCat.of Λ (CharacterModule
      ((Ambient.cohomology Λ X ηbar n).obj (CompactRepresentation.continuousDual Λ
        (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar))) K))) :=
  CompactRepresentation.compactHomologyCharacterIso Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar))
      ((restriction Λ X ηbar).obj K)
      (injectiveResolution (CompactRepresentation.continuousDual Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar))
        ((restriction Λ X ηbar).obj K))) n ≪≫
    (CharacterModule.congr
      (((CategoryTheory.Action.ModuleCat.DiscreteModuleCat.derivedCohomologyFunctor Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar)) n).mapIso
        (characterRestrictionIso Λ X ηbar K)).symm.toLinearEquiv)).toModuleIso

/-- The higher evaluation comparison is equivariant for the independently derived
compact quotient action and the contragredient relative-invariants action. -/
theorem residualCharacterIso_equivariant
    (K : CompactRepresentation.Cat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar))))
    (n : ℕ) (σ : Gal(AlgebraicClosure k/k)) :
    (((CompactModule.forget Λ).mapAction Gal(AlgebraicClosure k/k)).obj
        (geometricHomologyGaloisAction Λ X ηbar K n)).ρ σ ≫
      (residualCharacterIso Λ X ηbar K n).hom =
    (residualCharacterIso Λ X ηbar K n).hom ≫
      (characterGaloisAction Λ
        (AmbientGeometry.continuousCohomologyGaloisAction Λ X ηbar
          (CompactRepresentation.continuousDual Λ
            (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar))) K) n)).ρ σ := sorry

/-- The actual residual-equivariant character-duality isomorphism for compact homology. -/
def residualCharacterGaloisIso
    (K : CompactRepresentation.Cat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))) (n : ℕ) :
    ((CompactModule.forget Λ).mapAction Gal(AlgebraicClosure k/k)).obj
      (geometricHomologyGaloisAction Λ X ηbar K n) ≅
    characterGaloisAction Λ
      (AmbientGeometry.continuousCohomologyGaloisAction Λ X ηbar
        (CompactRepresentation.continuousDual Λ
          (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar))) K) n) :=
  Action.mkIso (residualCharacterIso Λ X ηbar K n) (residualCharacterIso_equivariant Λ X ηbar K n)

/-- Character transport along an actual equivariant linear isomorphism, with
the forward map given by precomposition with its inverse. -/
def characterGaloisIso
    {V W : Action (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k)} (e : V ≅ W) :
    characterGaloisAction Λ V ≅ characterGaloisAction Λ W :=
  Action.mkIso
    (CharacterModule.congr ((Action.forget (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k)).mapIso e).toLinearEquiv).toModuleIso
    (fun _ ↦ sorry)

end AlgebraicGeometry.SchemeOverField.CompactResidual
