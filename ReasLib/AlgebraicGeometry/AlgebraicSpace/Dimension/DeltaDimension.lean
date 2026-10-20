module

public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.WithBotTop
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.Sober
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.UniversallyCatenary
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Sober
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoints
public import ReasLib.Topology.Sober.IrreducibleComponent

/-!
# Dimensions of closed subsets of algebraic spaces

The dimension of an irreducible closed subset is the relative dimension function
at its generic point. Dimensions extend to arbitrary closed subsets by taking
suprema over irreducible components, and to closed subspaces through their supports.
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
  Iff.rfl

namespace Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}

/-- A generic point of an irreducible closed subset of the source point space of a
quasi-separated, locally of finite type morphism to a quasi-separated algebraic space. -/
noncomputable def genericPoint_of_good [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (T : IrreducibleCloseds (Points X)) :
    Points X :=
  @IsIrreducible.genericPoint (Points X) _ (points_sober_of_quasiSeparated f).2
    T.carrier T.isIrreducible

/-- `genericPoint_of_good f T` is a generic point of `T`. -/
theorem isGenericPoint_genericPoint_of_good [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (T : IrreducibleCloseds (Points X)) :
    IsGenericPoint (genericPoint_of_good f T) T.carrier :=
  @IsIrreducible.isGenericPoint_genericPoint (Points X) _
    (points_sober_of_quasiSeparated f).2 T.carrier T.isIrreducible T.isClosed

/-- The `δ`-dimension of an irreducible closed subset of `|X|`, evaluated at its generic
point via the relative dimension function of the morphism. -/
noncomputable def deltaDimension [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (T : IrreducibleCloseds (Points X)) : ℤ :=
  (relativeDimensionFunction f) δ (genericPoint_of_good f T)

/-- The dimension of an irreducible closed subset is the relative dimension function
at its chosen generic point. -/
theorem deltaDimension_def [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (T : IrreducibleCloseds (Points X)) :
    (deltaDimension f) δ T = (relativeDimensionFunction f) δ (genericPoint_of_good f T) :=
  rfl

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

/-- The dimension of a closed subset is the supremum of the dimensions of its
irreducible components. -/
theorem closedSetDeltaDimension_eq_iSup_irreducibleComponents
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (T : Closeds (Points X)) :
    (closedSetDeltaDimension f) δ T =
      ⨆ C : closedSetIrreducibleComponents T, ((deltaDimension f) δ C.1 : EInt) :=
  rfl

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
  rfl

/-- Comparison with the generic-point supremum formula on a closed subspace. -/
theorem closedSubspaceDeltaDimension_eq_iSup_genericPoints [UniversallyCatenary B]
    [IsQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (Z : ClosedSubspace X) :
    (closedSubspaceDeltaDimension f) δ Z =
      ⨆ η : genericPoints Z.X,
        ((relativeDimensionFunction f) δ (Points.map Z.ι η.1) : EInt) :=
  sorry

/-- A point of a closed subset whose relative dimension-function value attains an
integer upper bound for its `δ`-dimension is a generic point of an irreducible component. -/
@[stacks 0EE6]
theorem ofIrreducibleComponent_of_closedSetDeltaDimension_le
    {S : Scheme.{u}} {B X : AlgebraicSpace S} [UniversallyCatenary B]
    [IsQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (T : Closeds (Points X))
    (t : Points X) (ht : t ∈ T) (k : ℤ)
    (hdim : (closedSetDeltaDimension f) δ T ≤ (k : EInt))
    (htk : (relativeDimensionFunction f) δ t = k) :
    IsGenericPoint.ofIrreducibleComponent t T.carrier := sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
