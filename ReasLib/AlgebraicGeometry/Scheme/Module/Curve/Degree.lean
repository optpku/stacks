/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Degrees of vector bundles on proper curves

The degree of a finite locally free module on a proper curve is its Euler characteristic relative
to the structure sheaf, normalized by the rank.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

section

variable {k : Type u} [Field k]
variable {X : Scheme.{u}}

/-- The degree of a finite locally free module of rank `n` on a proper scheme of dimension at most
one is `χ(X, ℰ) - n χ(X, 𝒪_X)`. -/
@[stacks 0AYR]
def curveDegree (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (_ : topologicalKrullDim X ≤ 1) (ℰ : X.Modules) (n : ℕ)
    [IsFiniteLocallyFreeOfRank n ℰ] : ℤ :=
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : ℰ.IsCoherent := isCoherent_of_isFiniteLocallyFreeOfRank n ℰ
  Scheme.Hom.eulerCharacteristic f ℰ -
    (n : ℤ) * Scheme.Hom.eulerCharacteristic f
      (SheafOfModules.unit X.ringCatSheaf : X.Modules)

/-- The defining normal form for `curveDegree`. -/
@[stacks 0AYR]
theorem curveDegree_def (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (ℰ : X.Modules) (n : ℕ)
    [IsFiniteLocallyFreeOfRank n ℰ] :
    let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    let _ : ℰ.IsCoherent := isCoherent_of_isFiniteLocallyFreeOfRank n ℰ
    curveDegree f hdim ℰ n =
      Scheme.Hom.eulerCharacteristic f ℰ -
        (n : ℤ) * Scheme.Hom.eulerCharacteristic f
          (SheafOfModules.unit X.ringCatSheaf : X.Modules) := sorry

/-- For an invertible module on a proper scheme of dimension at most one, the degree is its Euler
characteristic relative to the structure sheaf. -/
@[stacks 0AYR]
theorem curveDegree_eq_eulerCharacteristic_sub_structureSheaf_of_invertible
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (ℒ : X.Modules) [Invertible ℒ] :
    let _ : IsFiniteLocallyFreeOfRank 1 ℒ :=
      isFiniteLocallyFreeOfRankOne_of_invertible ℒ
    let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    let _ : ℒ.IsCoherent := isCoherent_of_isFiniteLocallyFreeOfRank 1 ℒ
    curveDegree f hdim ℒ 1 =
      Scheme.Hom.eulerCharacteristic f ℒ -
        Scheme.Hom.eulerCharacteristic f
          (SheafOfModules.unit X.ringCatSheaf : X.Modules) := sorry

/-- The degree of an invertible module on a proper scheme of dimension at most one, using its
canonical rank-one finite locally free structure. -/
noncomputable def curveDegreeOfInvertible
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (ℒ : X.Modules) [Invertible ℒ] : ℤ :=
  let _ : IsFiniteLocallyFreeOfRank 1 ℒ :=
    isFiniteLocallyFreeOfRankOne_of_invertible ℒ
  curveDegree f hdim ℒ 1

/-- The degree of an invertible module is its Euler characteristic relative to the structure
sheaf. -/
theorem curveDegreeOfInvertible_eq_eulerCharacteristic_sub_structureSheaf
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (ℒ : X.Modules) [Invertible ℒ] :
    curveDegreeOfInvertible f hdim ℒ =
      Scheme.Hom.eulerCharacteristic f ℒ -
        Scheme.Hom.eulerCharacteristic f
          (SheafOfModules.unit X.ringCatSheaf : X.Modules) := sorry

/-- Curve degree is additive along a short exact complex of finite locally free modules of
constant rank on a proper scheme over a field of topological Krull dimension at most one. -/
@[stacks 0AYS]
theorem curveDegree_eq_add_of_shortExact_of_properOverField
    {S : ShortComplex X.Modules} {n₁ n₂ n₃ : ℕ}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    [IsFiniteLocallyFreeOfRank n₁ S.X₁]
    [IsFiniteLocallyFreeOfRank n₂ S.X₂]
    [IsFiniteLocallyFreeOfRank n₃ S.X₃]
    (hS : S.ShortExact) :
    curveDegree f hdim S.X₂ n₂ =
      curveDegree f hdim S.X₁ n₁ + curveDegree f hdim S.X₃ n₃ := sorry

namespace Invertible

/-- An explicit invertibility witness gives the canonical degree of its module on a proper
scheme of dimension at most one. -/
noncomputable def curveDegree {ℒ : X.Modules} (hℒ : Invertible ℒ)
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) : ℤ :=
  @curveDegreeOfInvertible k _ X f _ hdim ℒ hℒ

/-- The degree computed from an explicit invertibility witness agrees with the canonical
degree of the invertible module. -/
theorem curveDegree_eq (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (ℒ : X.Modules) [hℒ : Invertible ℒ] :
    hℒ.curveDegree f hdim = curveDegreeOfInvertible f hdim ℒ := sorry

end Invertible

end

end AlgebraicGeometry.Scheme.Modules
