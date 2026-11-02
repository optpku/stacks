/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.SquareZeroMap
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Residue
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.ResidueMap
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber

/-!
# Finite-dimensionality of residue derivations

Base-linear derivations from a Noetherian complete local algebra into its identified
residue field form a finite-dimensional vector space over that field.
-/

@[expose] public section

open scoped Module.CommOpposite

open CategoryTheory TrivSqZeroExt

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- The base-linear derivations of a complete local algebra into its identified residue field
form a finite-dimensional vector space over the residue field. -/
instance finiteDimensional_derivation (S : CompleteLocalAlgCat Λ k) :
    FiniteDimensional k (Derivation Λ S.carrier k) := sorry

noncomputable section

/-- A coefficient space has the scalar action of a complete local algebra through its residue map. -/
instance (priority := 80) instModule_carrier_of_residue (S : CompleteLocalAlgCat Λ k)
    (V : Type u) [AddCommGroup V] [Module k V] : Module S.carrier V :=
  Module.compHom V (residueFieldHom S).toRingHom

/-- The residue-induced scalar action is compatible with restriction of the base action. -/
instance instIsScalarTower_carrier_residue_module (S : CompleteLocalAlgCat Λ k)
    (V : Type u) [AddCommGroup V] [Module k V] [Module Λ V] [IsScalarTower Λ k V] :
    IsScalarTower Λ S.carrier V := sorry

/-- Residue-field scalars commute with the residue-induced complete local algebra action. -/
instance instSMulCommClass_residue_module (S : CompleteLocalAlgCat Λ k)
    (V : Type u) [AddCommGroup V] [Module k V] :
    SMulCommClass k S.carrier V := sorry

/-- The infinitesimal component of a residue-compatible square-zero morphism is a derivation. -/
def homToDerivation (S : CompleteLocalAlgCat Λ k) (V : Type u)
    [AddCommGroup V] [Module k V] [Module Λ V] [IsScalarTower Λ k V] [Module.Finite k V]
    (f : S ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.squareZero Λ k V)) :
    Derivation Λ S.carrier V := by
  let derivative := fun s : S.carrier ↦ (f.hom s).snd
  have laws : (∀ s t, derivative (s + t) = derivative s + derivative t) ∧
      (∀ scalar : Λ, ∀ s, derivative (scalar • s) = scalar • derivative s) ∧
      derivative 1 = 0 ∧
      (∀ s t, derivative (s * t) = s • derivative t + t • derivative s) := by
    sorry
  exact
    { toFun := derivative
      map_add' := laws.1
      map_smul' := laws.2.1
      map_one_eq_zero' := laws.2.2.1
      leibniz' := laws.2.2.2 }

/-- The associated derivation evaluates to the infinitesimal component of the morphism. -/
theorem homToDerivation_apply (S : CompleteLocalAlgCat Λ k) (V : Type u)
    [AddCommGroup V] [Module k V] [Module Λ V] [IsScalarTower Λ k V] [Module.Finite k V]
    (f : S ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.squareZero Λ k V))
    (s : S.carrier) :
    homToDerivation S V f s = (f.hom s).snd := rfl

/-- A derivation defines a square-zero morphism by adjoining its value to the residue component. -/
def derivationToHom (S : CompleteLocalAlgCat Λ k) (V : Type u)
    [AddCommGroup V] [Module k V] [Module Λ V] [IsScalarTower Λ k V] [Module.Finite k V]
    (D : Derivation Λ S.carrier V) :
    S ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.squareZero Λ k V) := by
  let target := ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.squareZero Λ k V)
  let value := fun s : S.carrier ↦ (inl (residueFieldHom S s) + inr (D s) : TrivSqZeroExt k V)
  have laws : value 1 = 1 ∧ (∀ s t, value (s * t) = value s * value t) ∧
      value 0 = 0 ∧ (∀ s t, value (s + t) = value s + value t) ∧
      (∀ scalar : Λ, value (algebraMap Λ S.carrier scalar) =
        algebraMap Λ (TrivSqZeroExt k V) scalar) ∧
      (∀ hom : algebraHom S target, (∀ s, hom s = value s) →
        IsLocalHom hom ∧ (∀ localness : IsLocalHom hom,
          residueCompat (A := S) (B := target) hom localness = residueIsoHom S)) := by
    sorry
  let hom : algebraHom S target :=
    { toFun := value, map_one' := laws.1, map_mul' := laws.2.1,
      map_zero' := laws.2.2.1, map_add' := laws.2.2.2.1,
      commutes' := laws.2.2.2.2.1 }
  exact Hom.of hom (laws.2.2.2.2.2 hom (fun _ ↦ rfl)).1
    ((laws.2.2.2.2.2 hom (fun _ ↦ rfl)).2 (laws.2.2.2.2.2 hom (fun _ ↦ rfl)).1)

/-- The reconstructed square-zero morphism has the prescribed residue and derivation components. -/
theorem derivationToHom_apply (S : CompleteLocalAlgCat Λ k) (V : Type u)
    [AddCommGroup V] [Module k V] [Module Λ V] [IsScalarTower Λ k V] [Module.Finite k V]
    (D : Derivation Λ S.carrier V) (s : S.carrier) :
    (derivationToHom S V D).hom s = inl (residueFieldHom S s) + inr (D s) := rfl

/-- The reconstructed square-zero morphism preserves the canonical augmentation to the residue field. -/
theorem derivationToHom_comp_squareZeroToResidue (S : CompleteLocalAlgCat Λ k)
    (V : Type u) [AddCommGroup V] [Module k V] [Module Λ V] [IsScalarTower Λ k V]
    [Module.Finite k V] (D : Derivation Λ S.carrier V) :
    derivationToHom S V D ≫
        ArtinianLocalAlgCat.inclusion.map (ArtinianLocalAlgCat.squareZeroToResidue Λ k V) =
      residueHom S := sorry

/-- Residue-compatible square-zero morphisms correspond to base-linear derivations. -/
def homEquivDerivation (S : CompleteLocalAlgCat Λ k) (V : Type u)
    [AddCommGroup V] [Module k V] [Module Λ V] [IsScalarTower Λ k V] [Module.Finite k V] :
    (S ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.squareZero Λ k V)) ≃
      Derivation Λ S.carrier V := by
  have laws : Function.LeftInverse (derivationToHom S V) (homToDerivation S V) ∧
      Function.RightInverse (derivationToHom S V) (homToDerivation S V) := by
    sorry
  exact Equiv.mk (homToDerivation S V) (derivationToHom S V) laws.1 laws.2

/-- The square-zero correspondence sends a morphism to its infinitesimal-component derivation. -/
theorem homEquivDerivation_apply (S : CompleteLocalAlgCat Λ k) (V : Type u)
    [AddCommGroup V] [Module k V] [Module Λ V] [IsScalarTower Λ k V] [Module.Finite k V]
    (f : S ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.squareZero Λ k V)) :
    homEquivDerivation S V f = homToDerivation S V f := rfl

/-- The inverse square-zero correspondence reconstructs a morphism from a derivation. -/
theorem homEquivDerivation_symm_apply (S : CompleteLocalAlgCat Λ k) (V : Type u)
    [AddCommGroup V] [Module k V] [Module Λ V] [IsScalarTower Λ k V] [Module.Finite k V]
    (D : Derivation Λ S.carrier V) :
    (homEquivDerivation S V).symm D = derivationToHom S V D := rfl

/-- The square-zero correspondence is natural under linear maps of coefficient spaces. -/
theorem homEquivDerivation_naturality (S : CompleteLocalAlgCat Λ k) (V W : Type u)
    [AddCommGroup V] [Module k V] [Module Λ V] [IsScalarTower Λ k V] [Module.Finite k V]
    [AddCommGroup W] [Module k W] [Module Λ W] [IsScalarTower Λ k W] [Module.Finite k W]
    (linearMap : V →ₗ[k] W)
    (f : S ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.squareZero Λ k V))
    (s : S.carrier) :
    homEquivDerivation S W
        (f ≫ ArtinianLocalAlgCat.inclusion.map (ArtinianLocalAlgCat.squareZeroMap linearMap)) s =
      linearMap (homEquivDerivation S V f s) := sorry

/-- The infinitesimal component of a dual-number morphism is a residue-valued derivation. -/
def dualNumberHomToDerivation (S : CompleteLocalAlgCat Λ k)
    (f : S ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.dualNumber Λ k)) :
    Derivation Λ S.carrier k := by
  let derivative := fun s : S.carrier ↦ (f.hom s).snd
  have laws : (∀ s t, derivative (s + t) = derivative s + derivative t) ∧
      (∀ scalar : Λ, ∀ s, derivative (scalar • s) = scalar • derivative s) ∧
      derivative 1 = 0 ∧
      (∀ s t, derivative (s * t) = s • derivative t + t • derivative s) := by
    sorry
  exact
    { toFun := derivative
      map_add' := laws.1
      map_smul' := laws.2.1
      map_one_eq_zero' := laws.2.2.1
      leibniz' := laws.2.2.2 }

/-- The residue-valued derivation evaluates to the infinitesimal component of a dual-number morphism. -/
theorem dualNumberHomToDerivation_apply (S : CompleteLocalAlgCat Λ k)
    (f : S ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.dualNumber Λ k))
    (s : S.carrier) :
    dualNumberHomToDerivation S f s = (f.hom s).snd := rfl

/-- A residue-valued derivation defines a dual-number morphism with the canonical residue component. -/
def dualNumberDerivationToHom (S : CompleteLocalAlgCat Λ k)
    (D : Derivation Λ S.carrier k) :
    S ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.dualNumber Λ k) := by
  let target := ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.dualNumber Λ k)
  let value := fun s : S.carrier ↦ (inl (residueFieldHom S s) + inr (D s) : TrivSqZeroExt k k)
  have laws : value 1 = 1 ∧ (∀ s t, value (s * t) = value s * value t) ∧
      value 0 = 0 ∧ (∀ s t, value (s + t) = value s + value t) ∧
      (∀ scalar : Λ, value (algebraMap Λ S.carrier scalar) =
        algebraMap Λ (TrivSqZeroExt k k) scalar) ∧
      (∀ hom : algebraHom S target, (∀ s, hom s = value s) →
        IsLocalHom hom ∧ (∀ localness : IsLocalHom hom,
          residueCompat (A := S) (B := target) hom localness = residueIsoHom S)) := by
    sorry
  let hom : algebraHom S target :=
    { toFun := value, map_one' := laws.1, map_mul' := laws.2.1,
      map_zero' := laws.2.2.1, map_add' := laws.2.2.2.1,
      commutes' := laws.2.2.2.2.1 }
  exact Hom.of hom (laws.2.2.2.2.2 hom (fun _ ↦ rfl)).1
    ((laws.2.2.2.2.2 hom (fun _ ↦ rfl)).2 (laws.2.2.2.2.2 hom (fun _ ↦ rfl)).1)

/-- The reconstructed dual-number morphism has the prescribed residue and infinitesimal components. -/
theorem dualNumberDerivationToHom_apply (S : CompleteLocalAlgCat Λ k)
    (D : Derivation Λ S.carrier k) (s : S.carrier) :
    (dualNumberDerivationToHom S D).hom s = inl (residueFieldHom S s) + inr (D s) := rfl

/-- Dual-number morphisms correspond to residue-valued base-linear derivations. -/
def dualNumberHomEquivDerivation (S : CompleteLocalAlgCat Λ k) :
    (S ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.dualNumber Λ k)) ≃
      Derivation Λ S.carrier k := by
  have laws : Function.LeftInverse (dualNumberDerivationToHom S) (dualNumberHomToDerivation S) ∧
      Function.RightInverse (dualNumberDerivationToHom S) (dualNumberHomToDerivation S) := by
    sorry
  exact Equiv.mk (dualNumberHomToDerivation S) (dualNumberDerivationToHom S) laws.1 laws.2

/-- The dual-number correspondence sends a morphism to its infinitesimal-component derivation. -/
theorem dualNumberHomEquivDerivation_apply (S : CompleteLocalAlgCat Λ k)
    (f : S ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.dualNumber Λ k)) :
    dualNumberHomEquivDerivation S f = dualNumberHomToDerivation S f := rfl

/-- The inverse dual-number correspondence reconstructs a morphism from a residue-valued derivation. -/
theorem dualNumberHomEquivDerivation_symm_apply (S : CompleteLocalAlgCat Λ k)
    (D : Derivation Λ S.carrier k) :
    (dualNumberHomEquivDerivation S).symm D = dualNumberDerivationToHom S D := rfl

end

end CompleteLocalAlgCat
