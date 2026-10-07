module

public import Mathlib.Order.KrullDimension
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober
public import ReasLib.Topology.IrreducibleCloseds.Soberification.Basic
public import ReasLib.Topology.Specialization.Dimension
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap66.Definition_66_19_1_GeometricPoint
public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap66.Lemma_66_10_3_LocalRingDim
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap68.Definition_68_25_4_UniversallyCatenary
public import stacks_project.Chap68.Lemma_68_23_1_Jacobson
public import stacks_project.Chap72.Definition_72_4_1_Integral
public import stacks_project.Chap76.Lemma_76_32_2_DimensionFunction

/-!
# Relative dimension of integral closed subspaces over Jacobson bases

In the good setup over a Jacobson universally catenary base whose dimension
function vanishes on closed points, the relative dimension at the generic
point of an integral closed subspace equals the topological, codimension,
local-ring, and étale-local-ring dimensions of that subspace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Lemma 82.2.4 (1): in Situation 82.2.1, if `B` is Jacobson and `δ b = 0` for
every closed point `b` of `Points B`, then for a good morphism `f : X ⟶ B` and
an integral closed subspace `Z ⊂ X` with generic point `ξ` of `Points Z.X`,
the value `f.relativeDimensionFunction δ (Points.map Z.ι ξ)` equals the
integer cast of its `Int.toNat`. -/
@[stacks 0EDW]
theorem relativeDimensionFunction_generic_eq_natCast {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    [IsJacobson B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (hδ_closed : ∀ b ∈ closedPoints (Points B), δ b = 0)
    (Z : ClosedSubspace X) [IsIntegral Z.X] (ξ : Points Z.X)
    (hξ : IsGenericPoint ξ (Set.univ : Set (Points Z.X))) :
    f.relativeDimensionFunction δ (Points.map Z.ι ξ) =
      (Int.toNat (f.relativeDimensionFunction δ (Points.map Z.ι ξ)) : ℤ) :=
  sorry

/-- Lemma 82.2.4 (2): in the same setup, `topologicalKrullDim (Points Z.X)` equals
the `Int.toNat` of `f.relativeDimensionFunction δ (Points.map Z.ι ξ)`, as an
element of `WithBot ℕ∞`. -/
@[stacks 0EDW]
theorem topologicalKrullDim_eq_relativeDimensionFunction_generic {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    [IsJacobson B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (hδ_closed : ∀ b ∈ closedPoints (Points B), δ b = 0)
    (Z : ClosedSubspace X) [IsIntegral Z.X] (ξ : Points Z.X)
    (hξ : IsGenericPoint ξ (Set.univ : Set (Points Z.X))) :
    topologicalKrullDim (Points Z.X) =
      (Int.toNat (f.relativeDimensionFunction δ (Points.map Z.ι ξ)) : WithBot ℕ∞) :=
  sorry

/-- Lemma 82.2.4 (3): in the same setup, for every closed point `z` of
`Points Z.X`, the coheight of `toIrreducibleCloseds z` equals the `Int.toNat`
of `f.relativeDimensionFunction δ (Points.map Z.ι ξ)`. -/
@[stacks 0EDW]
theorem coheight_closedPoint_eq_relativeDimensionFunction_generic {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    [IsJacobson B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (hδ_closed : ∀ b ∈ closedPoints (Points B), δ b = 0)
    (Z : ClosedSubspace X) [IsIntegral Z.X] (ξ : Points Z.X)
    (hξ : IsGenericPoint ξ (Set.univ : Set (Points Z.X)))
    (z : Points Z.X) (hz : z ∈ closedPoints (Points Z.X)) :
    (Order.coheight (toIrreducibleCloseds z) : WithBot ℕ∞) =
      (Int.toNat (f.relativeDimensionFunction δ (Points.map Z.ι ξ)) : WithBot ℕ∞) :=
  sorry

/-- Lemma 82.2.4 (4): in the same setup, for every closed point `z` of
`Points Z.X`, `localRingDimAt z` equals the `Int.toNat` of
`f.relativeDimensionFunction δ (Points.map Z.ι ξ)`. -/
@[stacks 0EDW]
theorem localRingDimAt_eq_relativeDimensionFunction_generic {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    [IsJacobson B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (hδ_closed : ∀ b ∈ closedPoints (Points B), δ b = 0)
    (Z : ClosedSubspace X) [IsIntegral Z.X] (ξ : Points Z.X)
    (hξ : IsGenericPoint ξ (Set.univ : Set (Points Z.X)))
    (z : Points Z.X) (hz : z ∈ closedPoints (Points Z.X)) :
    localRingDimAt z =
      (Int.toNat (f.relativeDimensionFunction δ (Points.map Z.ι ξ)) : WithBot ℕ∞) :=
  sorry

/-- Lemma 82.2.4 (5): in the same setup, for every closed point `z` of
`Points Z.X` and every geometric point `zbar` of `Z.X` lying over `z`,
`ringKrullDim (etaleLocalRing Z.X zbar)` equals the `Int.toNat` of
`f.relativeDimensionFunction δ (Points.map Z.ι ξ)`. -/
@[stacks 0EDW]
theorem ringKrullDim_etaleLocalRing_eq_relativeDimensionFunction_generic
    {S : Scheme.{u}} {B X : AlgebraicSpace S} [UniversallyCatenary B]
    [IsQuasiSeparated B] [IsJacobson B] (f : X ⟶ B) [QuasiSeparated f]
    [LocallyOfFiniteType f] (δ : Points B → ℤ) [IsDimensionFunction δ]
    (hδ_closed : ∀ b ∈ closedPoints (Points B), δ b = 0)
    (Z : ClosedSubspace X) [IsIntegral Z.X] (ξ : Points Z.X)
    (hξ : IsGenericPoint ξ (Set.univ : Set (Points Z.X)))
    (z : Points Z.X) (hz : z ∈ closedPoints (Points Z.X))
    (zbar : GeometricPoint Z.X) (hzbar : zbar.liesOver z) :
    ringKrullDim (etaleLocalRing Z.X zbar) =
      (Int.toNat (f.relativeDimensionFunction δ (Points.map Z.ι ξ)) : WithBot ℕ∞) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
