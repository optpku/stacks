/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Genus
public import ReasLib.AlgebraicGeometry.Scheme.OverField.GeometricGenus
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Multicross
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.FieldRamification

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- For a proper reduced connected one-dimensional scheme over an algebraically closed field,
the prime-to-characteristic Picard torsion has dimension at most the arithmetic genus plus the
sum of the geometric genera of the irreducible components. -/
theorem picardTorsionFinrankLe
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [IsProper X.hom] [IsReduced X.left] [ConnectedSpace X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (g g_geom ℓ : ℕ) [Fact ℓ.Prime]
    (h_genus : g = SchemeOverField.genus X h_dimension hΓ)
    (h_geometricGenus : g_geom = GeometricGenus.ofScheme X h_dimension.le)
    (h_prime_to_char : DVR.Field.PrimeToChar k ℓ) :
    @Module.finrank (ZMod ℓ)
        (AddSubgroup.torsionBy X.left.PicardGroup (ℓ : ℤ)) _ _
        (AddSubgroup.torsionBy.zmodModule :
          Module (ZMod ℓ) (AddSubgroup.torsionBy X.left.PicardGroup (ℓ : ℤ))) ≤
      g + g_geom := sorry

/-- For a proper reduced connected one-dimensional scheme over an algebraically closed field,
equality in the Picard-torsion bound holds exactly when every singular point is multicross. -/
theorem picardTorsionFinrankEqIff
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [IsProper X.hom] [IsReduced X.left] [ConnectedSpace X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (g g_geom ℓ : ℕ) [Fact ℓ.Prime]
    (h_genus : g = SchemeOverField.genus X h_dimension hΓ)
    (h_geometricGenus : g_geom = GeometricGenus.ofScheme X h_dimension.le)
    (h_prime_to_char : DVR.Field.PrimeToChar k ℓ) :
    @Module.finrank (ZMod ℓ)
        (AddSubgroup.torsionBy X.left.PicardGroup (ℓ : ℤ)) _ _
        (AddSubgroup.torsionBy.zmodModule :
          Module (ZMod ℓ) (AddSubgroup.torsionBy X.left.PicardGroup (ℓ : ℤ))) =
      g + g_geom ↔
      ∀ x : X.left, ¬ X.hom.SmoothAt x → isMulticrossSingularity X x := sorry

end AlgebraicGeometry.SchemeOverField

end
