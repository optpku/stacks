/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.WithBotTop
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.Sober
public import ReasLib.Topology.Specialization.Dimension
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap66.Lemma_66_12_3
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap68.Definition_68_22_1_GenericPoints
public import stacks_project.Chap68.Definition_68_25_4_UniversallyCatenary
public import stacks_project.Chap76.Lemma_76_32_2_DimensionFunction
public import stacks_project.Chap82.Remark_82_2_2

/-!
# δ-dimension of closed subsets of algebraic spaces

In the good setup of Situation 82.2.1, the δ-dimension of an irreducible closed
subset of `|X|` is the relative dimension function at its generic point. This
extends by supremum over irreducible components to arbitrary closed subsets, and
to closed subspaces by their underlying point-sets.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Irreducible components of a closed set of `|X|`, as irreducible closed subsets of `|X|`. -/
def closedSetIrreducibleComponents {S : Scheme.{u}} {X : AlgebraicSpace S}
    (T : Closeds (Points X)) : Set (IrreducibleCloseds (Points X)) :=
  {C | Maximal (fun s : Set (Points X) ↦ IsIrreducible s ∧ s ⊆ T.carrier) C.carrier}

/-- Membership in `closedSetIrreducibleComponents T` is maximality among irreducible
subsets of `T`. -/
theorem mem_closedSetIrreducibleComponents {S : Scheme.{u}} {X : AlgebraicSpace S}
    {T : Closeds (Points X)} {C : IrreducibleCloseds (Points X)} :
    C ∈ closedSetIrreducibleComponents T ↔
      Maximal (fun s : Set (Points X) ↦ IsIrreducible s ∧ s ⊆ T.carrier) C.carrier :=
  sorry

namespace Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}

/-- The generic point of an irreducible closed subset of `|X|` in the good setup. -/
noncomputable def genericPoint_of_good [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (T : IrreducibleCloseds (Points X)) :
    Points X :=
  @IsIrreducible.genericPoint (Points X) _ (points_sober_of_quasiSeparated f).2
    T.carrier T.isIrreducible

/-- `genericPoint_of_good f T` is a generic point of `T`. -/
theorem isGenericPoint_genericPoint_of_good [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (T : IrreducibleCloseds (Points X)) :
    IsGenericPoint (genericPoint_of_good f T) T.carrier :=
  sorry

/-- The `δ`-dimension of an irreducible closed subset of `|X|`, evaluated at its generic
point via the relative dimension function of a good morphism. -/
noncomputable def deltaDimension [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (T : IrreducibleCloseds (Points X)) : ℤ :=
  (relativeDimensionFunction f) δ (genericPoint_of_good f T)

/-- Unfolding of `deltaDimension` to the relative dimension function at
`genericPoint_of_good`. -/
theorem deltaDimension_def [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (T : IrreducibleCloseds (Points X)) :
    (deltaDimension f) δ T = (relativeDimensionFunction f) δ (genericPoint_of_good f T) :=
  sorry

/-- The `δ`-dimension of an irreducible closed subset may be evaluated at any generic point. -/
theorem deltaDimension_eq_of_isGenericPoint [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (T : IrreducibleCloseds (Points X)) (ξ : Points X)
    (hξ : IsGenericPoint ξ T.carrier) :
    (deltaDimension f) δ T = (relativeDimensionFunction f) δ ξ :=
  sorry

/-- The `δ`-dimension of a closed subset of `|X|` is the extended-integer supremum of the
`δ`-dimensions of its irreducible components. -/
noncomputable def closedSetDeltaDimension [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (T : Closeds (Points X)) : EInt :=
  ⨆ C : closedSetIrreducibleComponents T, ((deltaDimension f) δ C.1 : EInt)

/-- Unfolding of `closedSetDeltaDimension` as a supremum over irreducible components. -/
theorem closedSetDeltaDimension_eq_iSup_irreducibleComponents
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (T : Closeds (Points X)) :
    (closedSetDeltaDimension f) δ T =
      ⨆ C : closedSetIrreducibleComponents T, ((deltaDimension f) δ C.1 : EInt) :=
  sorry

/-- The `δ`-dimension of a closed subset equals the pointwise supremum of the relative
dimension function. -/
theorem closedSetDeltaDimension_eq_iSup [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (T : Closeds (Points X)) :
    (closedSetDeltaDimension f) δ T =
      ⨆ t : T, ((relativeDimensionFunction f) δ (t : Points X) : EInt) :=
  sorry

/-- On an irreducible closed subset, the closed-set `δ`-dimension is the extended-integer
coercion of `deltaDimension`. -/
theorem closedSetDeltaDimension_irreducibleCloseds [UniversallyCatenary B]
    [IsQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (T : IrreducibleCloseds (Points X)) :
    (closedSetDeltaDimension f) δ ⟨T.carrier, T.isClosed⟩ = ((deltaDimension f) δ T : EInt) :=
  sorry

/-- The `δ`-dimension of a closed subspace is the `δ`-dimension of its underlying point-set. -/
noncomputable def closedSubspaceDeltaDimension [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (Z : ClosedSubspace X) : EInt :=
  (closedSetDeltaDimension f) δ ⟨Z.pointsSet, Z.isClosed_pointsSet⟩

/-- The `δ`-dimension of a closed subspace equals the `δ`-dimension of `|Z|`. -/
theorem closedSubspaceDeltaDimension_eq_closedSet [UniversallyCatenary B]
    [IsQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (Z : ClosedSubspace X) :
    (closedSubspaceDeltaDimension f) δ Z =
      (closedSetDeltaDimension f) δ ⟨Z.pointsSet, Z.isClosed_pointsSet⟩ :=
  sorry

/-- Unfolding of `closedSubspaceDeltaDimension` as `closedSetDeltaDimension` of `|Z|`. -/
theorem closedSubspaceDeltaDimension_def [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (Z : ClosedSubspace X) :
    (closedSubspaceDeltaDimension f) δ Z =
      (closedSetDeltaDimension f) δ ⟨Z.pointsSet, Z.isClosed_pointsSet⟩ :=
  sorry

/-- Comparison with the generic-point supremum formula on a closed subspace. -/
theorem closedSubspaceDeltaDimension_eq_iSup_genericPoints [UniversallyCatenary B]
    [IsQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (Z : ClosedSubspace X) :
    (closedSubspaceDeltaDimension f) δ Z =
      ⨆ η : genericPoints Z.X,
        ((relativeDimensionFunction f) δ (Points.map Z.ι η.1) : EInt) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
