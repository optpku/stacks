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
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.FieldRamification
public import ReasLib.AlgebraicGeometry.Scheme.OverField.PicardTorsion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Proposition 53.17.3 (1): the Picard-torsion bound for a proper reduced connected
one-dimensional scheme over an algebraically closed field. -/
@[stacks 0C20] #check (AlgebraicGeometry.SchemeOverField.picardTorsionFinrankLe :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
      [IsProper X.hom] [IsReduced X.left] [ConnectedSpace X.left]
      (h_dimension : topologicalKrullDim X.left = 1)
      (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
      (g g_geom ℓ : ℕ) [Fact ℓ.Prime]
      (h_genus : g = AlgebraicGeometry.SchemeOverField.genus X h_dimension hΓ)
      (h_geometricGenus : g_geom = AlgebraicGeometry.GeometricGenus.ofScheme X h_dimension.le)
      (h_prime_to_char : DVR.Field.PrimeToChar k ℓ),
      @Module.finrank (ZMod ℓ)
          (AddSubgroup.torsionBy X.left.PicardGroup (ℓ : ℤ)) _ _
          (AddSubgroup.torsionBy.zmodModule :
            Module (ZMod ℓ) (AddSubgroup.torsionBy X.left.PicardGroup (ℓ : ℤ))) ≤
        g + g_geom)

/- Proposition 53.17.3 (2): equality in the Picard-torsion bound is equivalent to every
singular point being multicross. -/
@[stacks 0C20] #check (AlgebraicGeometry.SchemeOverField.picardTorsionFinrankEqIff :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
      [IsProper X.hom] [IsReduced X.left] [ConnectedSpace X.left]
      (h_dimension : topologicalKrullDim X.left = 1)
      (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
      (g g_geom ℓ : ℕ) [Fact ℓ.Prime]
      (h_genus : g = AlgebraicGeometry.SchemeOverField.genus X h_dimension hΓ)
      (h_geometricGenus : g_geom = AlgebraicGeometry.GeometricGenus.ofScheme X h_dimension.le)
      (h_prime_to_char : DVR.Field.PrimeToChar k ℓ),
      @Module.finrank (ZMod ℓ)
          (AddSubgroup.torsionBy X.left.PicardGroup (ℓ : ℤ)) _ _
          (AddSubgroup.torsionBy.zmodModule :
            Module (ZMod ℓ) (AddSubgroup.torsionBy X.left.PicardGroup (ℓ : ℤ))) =
        g + g_geom ↔
        ∀ x : X.left, ¬ X.hom.SmoothAt x →
          AlgebraicGeometry.SchemeOverField.isMulticrossSingularity X x)

end
