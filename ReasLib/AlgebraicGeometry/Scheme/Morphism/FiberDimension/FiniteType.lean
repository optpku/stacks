module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.GenericFiber
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension

/-!
# Dimensions of fibres of finite type morphisms

This leaf relates the local topological dimension of a scheme-theoretic fibre to the Krull
dimension of its stalk and the transcendence degree of the corresponding residue-field extension.
It also records boundedness and generic constancy results for dimensions of fibres.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

namespace FiberDimension

/-- For a locally finite type morphism, the local topological dimension at the distinguished
point of a fibre is the Krull dimension of its stalk plus the residue-field transcendence degree. -/
theorem topologicalAt_eq_stalk_add_trdeg
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) :
    topologicalKrullDimAt (f.asFiber x) =
      ringKrullDim (fiberStalkAt f x) + f.residueFieldTrdegAt x := sorry

/-- For a locally finite type morphism, the fibre dimension at a source point is the Krull
dimension of the fibre stalk plus the residue-field transcendence degree. -/
theorem at_eq_stalk_add_trdeg
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) :
    f.fiberDimensionAt x =
      ringKrullDim (fiberStalkAt f x) + f.residueFieldTrdegAt x := sorry

/-- In a fibre of a locally finite type morphism, a proper specialization strictly increases
the Krull dimension of the local ring. -/
theorem ringKrullDim_stalk_lt_of_specializes
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] {s : S}
    {x x' : f.fiber s} (hxx' : Specializes x x') (hneq : x ≠ x') :
    ringKrullDim ((f.fiber s).presheaf.stalk x) <
      ringKrullDim ((f.fiber s).presheaf.stalk x') := sorry

/-- In a fibre of a locally finite type morphism, a proper specialization strictly decreases
the residue-field transcendence degree over the base residue field. -/
theorem trdeg_residueField_gt_of_specializes
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] {s : S}
    {x x' : f.fiber s} (hxx' : Specializes x x') (hneq : x ≠ x') :
    Cardinal.toNat (Algebra.trdeg (S.residueField s) ((f.fiber s).residueField x)) >
      Cardinal.toNat (Algebra.trdeg (S.residueField s) ((f.fiber s).residueField x')) := sorry

end FiberDimension

/-- For a locally finite type morphism, the locus where the local fibre dimension is at most
`n` is open. -/
theorem isOpen_fiberDimensionLELocus
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (n : ℕ) :
    IsOpen (f.fiberDimensionLELocus n) := sorry

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Hom.FiniteType

/-- A finite type morphism to a quasi-compact scheme admits a uniform finite upper bound on the
local dimensions of its fibres. -/
theorem exists_fiberDimensionAt_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] [CompactSpace Y] :
    ∃ n : ℕ, ∀ x : X, f.fiberDimensionAt x ≤ (n : WithBot ℕ∞) := sorry

/-- If the generic fibre of a finite type morphism to an irreducible scheme has dimension `n`,
then all fibres over some nonempty open subset have dimension `n`. -/
@[stacks 05F7]
theorem exists_open_topologicalKrullDim_fiber_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] [IrreducibleSpace Y] {n : ℕ}
    (hη : topologicalKrullDim (f.fiber (genericPoint Y)) = (n : WithBot ℕ∞)) :
    ∃ V : Y.Opens, Nonempty V ∧ ∀ y : Y, y ∈ V →
      topologicalKrullDim (f.fiber y) = (n : WithBot ℕ∞) := sorry

end AlgebraicGeometry.Scheme.Hom.FiniteType
