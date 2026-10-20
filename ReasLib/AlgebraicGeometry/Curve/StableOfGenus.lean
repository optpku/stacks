/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Stable
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage

/-!
# Stable families of a given genus

This file records the unbundled property of being a stable family of curves of
genus `g`, uniqueness of that genus, the coproduct covering of stable curves
over a field by genus-`g` pieces, and the two standard geometric
characterizations over a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.SchemeOverField
open Scheme.DerivedQCoh.ProperDualizingComplex
open SheafOfModules
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes is a stable family of genus `g` when every residue-field
fibre is a stable curve and the first higher direct image of the structure sheaf
is finite locally free of rank `g`. -/
def IsStableFamilyOfGenus {X S : Scheme.{u}} (g : ℕ) (f : X ⟶ S) : Prop :=
  (∀ s : S, isStableCurve (Over.mk (f.fiberToSpecResidueField s))) ∧
    IsFiniteLocallyFreeOfRank g
      (higherDirectImageModule f.toShHom (unit X.ringCatSheaf) 1)

/-- A morphism is a stable family of genus `g` if and only if every residue-field
fibre is a stable curve and the first higher direct image of the structure sheaf
is finite locally free of rank `g`. -/
theorem isStableFamilyOfGenus_iff {X S : Scheme.{u}} (g : ℕ) (f : X ⟶ S) :
    IsStableFamilyOfGenus g f ↔
      (∀ s : S, isStableCurve (Over.mk (f.fiberToSpecResidueField s))) ∧
        IsFiniteLocallyFreeOfRank g
          (higherDirectImageModule f.toShHom (unit X.ringCatSheaf) 1) :=
  Iff.rfl

/-- A proper scheme of dimension at most one over a field is a stable curve if
and only if it is a stable family of some genus `g ≥ 2`. -/
theorem exists_isStableFamilyOfGenus_iff {k : Type u} [Field k]
    (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    isStableCurve X ↔ ∃ g : ℕ, IsStableFamilyOfGenus (g + 2) X.hom :=
  sorry

/-- Over a nonempty base, the locally free rank of a stable family of a given genus is unique,
so the genus-`g` pieces are disjoint. The base must be nonempty: over the empty scheme every
module sheaf is finite locally free of every rank, so the family has every genus. -/
theorem eq_of_isStableFamilyOfGenus {X S : Scheme.{u}} [Nonempty S] {f : X ⟶ S} {g g' : ℕ}
    (hg : IsStableFamilyOfGenus g f) (hg' : IsStableFamilyOfGenus g' f) :
    g = g' :=
  sorry

/-- A proper scheme of dimension at most one over a field is a stable family of
genus `g ≥ 2` if and only if it is at-worst-nodal of dimension one, has constant
global functions, has genus `g`, and has neither a rational tail nor a rational
bridge. -/
theorem isStableFamilyOfGenus_iff_atWorstNodal_genus
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (g : ℕ) (hg : 2 ≤ g) :
    IsStableFamilyOfGenus g X.hom ↔
      atWorstNodal X ∧
        ∃ (hdim1 : topologicalKrullDim X.left = 1)
          (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
          genus X hdim1 hΓ = g ∧
            ¬ Nonempty (RationalTail X) ∧ ¬ Nonempty (RationalBridge X) :=
  sorry

/-- A proper scheme of dimension at most one over a field is a stable family of
genus `g ≥ 2` if and only if it is at-worst-nodal of dimension one, has constant
global functions, has genus `g`, and has ample canonical dualizing module. -/
theorem isStableFamilyOfGenus_iff_curveDualizingModule_isAmple
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (g : ℕ) (hg : 2 ≤ g) :
    IsStableFamilyOfGenus g X.hom ↔
      atWorstNodal X ∧
        ∃ (hdim1 : topologicalKrullDim X.left = 1)
          (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
          genus X hdim1 hΓ = g ∧
            Scheme.Modules.isAmpleObject (curveDualizingModule X.hom) :=
  sorry

end AlgebraicGeometry
