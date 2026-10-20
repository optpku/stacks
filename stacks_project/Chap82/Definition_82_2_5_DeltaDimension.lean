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

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.DeltaDimension

/-!
# Compatibility checks for dimensions of closed subsets of algebraic spaces
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.closedSetIrreducibleComponents :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (T : Closeds (Points X)),
    Set (IrreducibleCloseds (Points X)))

#check (AlgebraicGeometry.AlgebraicSpace.mem_closedSetIrreducibleComponents :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {T : Closeds (Points X)} {C : IrreducibleCloseds (Points X)},
    C ∈ closedSetIrreducibleComponents T ↔
      Maximal (fun s : Set (Points X) ↦ IsIrreducible s ∧ s ⊆ T.carrier) C.carrier)

namespace Hom

#check (AlgebraicGeometry.AlgebraicSpace.Hom.genericPoint_of_good :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (T : IrreducibleCloseds (Points X)),
    Points X)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.isGenericPoint_genericPoint_of_good :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (T : IrreducibleCloseds (Points X)),
    IsGenericPoint (genericPoint_of_good f T) T.carrier)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.deltaDimension :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (T : IrreducibleCloseds (Points X)),
    ℤ)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.deltaDimension_def :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (T : IrreducibleCloseds (Points X)),
    (deltaDimension f) δ T = (relativeDimensionFunction f) δ (genericPoint_of_good f T))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.deltaDimension_eq_of_isGenericPoint :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (T : IrreducibleCloseds (Points X)) (ξ : Points X)
    (hξ : IsGenericPoint ξ T.carrier),
    (deltaDimension f) δ T = (relativeDimensionFunction f) δ ξ)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.closedSetDeltaDimension :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (T : Closeds (Points X)),
    EInt)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.closedSetDeltaDimension_eq_iSup_irreducibleComponents :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (T : Closeds (Points X)),
    (closedSetDeltaDimension f) δ T =
      ⨆ C : closedSetIrreducibleComponents T, ((deltaDimension f) δ C.1 : EInt))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.closedSetDeltaDimension_eq_iSup :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (T : Closeds (Points X)),
    (closedSetDeltaDimension f) δ T =
      ⨆ t : T, ((relativeDimensionFunction f) δ (t : Points X) : EInt))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.closedSetDeltaDimension_irreducibleCloseds :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} [UniversallyCatenary B]
    [IsQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (T : IrreducibleCloseds (Points X)),
    (closedSetDeltaDimension f) δ ⟨T.carrier, T.isClosed⟩ = ((deltaDimension f) δ T : EInt))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.closedSubspaceDeltaDimension :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (Z : ClosedSubspace X),
    EInt)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.closedSubspaceDeltaDimension_eq_closedSet :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} [UniversallyCatenary B]
    [IsQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (Z : ClosedSubspace X),
    (closedSubspaceDeltaDimension f) δ Z =
      (closedSetDeltaDimension f) δ ⟨Z.pointsSet, Z.isClosed_pointsSet⟩)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.closedSubspaceDeltaDimension_eq_iSup_genericPoints :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} [UniversallyCatenary B]
    [IsQuasiSeparated B] (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (Z : ClosedSubspace X),
    (closedSubspaceDeltaDimension f) δ Z =
      ⨆ η : genericPoints Z.X,
        ((relativeDimensionFunction f) δ (Points.map Z.ι η.1) : EInt))

end Hom

end AlgebraicGeometry.AlgebraicSpace
