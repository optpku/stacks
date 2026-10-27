/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Generated
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalTail
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Semistable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Nodal
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

/-!
# The semistable locus of curve families

Semistability is represented by an open of the base of every family of curves.
For proper schemes over fields, it is characterized by nodality, dimension,
global functions and the absence of rational tails, or by global generation
of dualizing tensor powers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.Scheme
open Scheme.DerivedQCoh.ProperDualizingComplex

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The dualizing module of a proper scheme over a field is invertible, and
every integral tensor power of exponent at least two is globally generated. -/
def dualizingTensorPowersGloballyGenerated {k : Type u} [Field k]
    (X : SchemeOverField k) [IsProper X.hom] : Prop :=
  ∃ (hL : Scheme.Modules.Invertible (dualizingModule X.hom)),
    ∀ (m : ℤ), 2 ≤ m →
      SheafOfModules.IsGloballyGenerated
        (@Scheme.Modules.tensorPowerInt X.left (dualizingModule X.hom) hL m)

/-- Semistability of families of curves is invariant under isomorphisms. -/
instance instIsClosedUnderIsomorphisms_semistable (S : Scheme.{u}) :
    (semistable S).IsClosedUnderIsomorphisms := sorry

/-- For every curve family, an open of its base represents semistability under every cartesian
morphism of curve families. -/
theorem exists_semistable_open {S : Scheme.{u}} (P : Obj S) :
    ∃ U : (base P).left.Opens, ∀ {Q : Obj S} (φ : Q ⟶ P),
      semistable S Q ↔ Set.range (baseMap φ).left ⊆ U := sorry

/-- A proper scheme of dimension at most one over a field is a semistable curve precisely
when it is nodal of dimension one, has constant global functions, has genus at least one,
and has no rational tails. -/
theorem classifying_factorsThrough_semistable_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    semistable (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.atWorstNodal X ∧
        ∃ (hdim1 : topologicalKrullDim X.left = 1)
          (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
          1 ≤ SchemeOverField.genus X hdim1 hΓ ∧
            ¬ Nonempty (SchemeOverField.RationalTail X) :=
  sorry

/-- A proper scheme of dimension at most one over a field is a semistable curve precisely
when it is nodal of dimension one, has constant global functions, and has invertible dualizing
module with all integral tensor powers of exponent at least two globally generated. -/
theorem classifying_factorsThrough_semistable_iff_scheme_dualizing
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    semistable (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.atWorstNodal X ∧
        topologicalKrullDim X.left = 1 ∧
        Function.Bijective (Scheme.Hom.globalSectionsMap X.hom) ∧
        dualizingTensorPowersGloballyGenerated X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
