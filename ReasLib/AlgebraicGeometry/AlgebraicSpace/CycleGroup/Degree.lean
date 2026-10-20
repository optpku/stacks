module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SpecField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.ProperPushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.Closure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.OverField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.IntegralImage

/-!
# Degree of zero-cycles on proper algebraic spaces

Degree is the coefficient of the unique point of the field spectrum after
proper pushforward along the structural morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The degree of a zero-cycle is its proper pushforward coefficient at the unique point
of the field spectrum. -/
def zeroCycleDegree {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Proper (SchemeRealization.toBase X)] :
    cycleGroup (SchemeRealization.toBase X) (fun _ ↦ (0 : ℤ)) 0 →+ ℤ :=
  AddMonoidHom.mk'
    (fun α ↦
      properPushforwardCycle (SchemeRealization.toBase X) (𝟙 _)
        (fun _ ↦ (0 : ℤ)) (SchemeRealization.toBase X)
        (Category.comp_id _)
        (α : Function.locallyFinsupp (Points X) ℤ) (Points.specFieldPoint k))
    (fun α β ↦ congrArg (fun γ ↦ γ (Points.specFieldPoint k))
      (properPushforwardCycle_add (SchemeRealization.toBase X) (𝟙 _)
        (fun _ ↦ (0 : ℤ)) (SchemeRealization.toBase X)
        (Category.comp_id _) α β))

/-- The degree of a zero-cycle evaluates the proper pushforward at the unique point
of the field spectrum. -/
theorem zeroCycleDegree_apply {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Proper (SchemeRealization.toBase X)]
    (α : cycleGroup (SchemeRealization.toBase X) (fun _ ↦ (0 : ℤ)) 0) :
    zeroCycleDegree α =
      properPushforwardCycle (SchemeRealization.toBase X) (𝟙 _)
        (fun _ ↦ (0 : ℤ)) (SchemeRealization.toBase X)
        (Category.comp_id _)
        (α : Function.locallyFinsupp (Points X) ℤ) (Points.specFieldPoint k) :=
  rfl

/-- The degree of a zero-cycle is the finite sum of its coefficients weighted by
the dimensions of the global-sections algebras of the reduced point closures. -/
theorem zeroCycleDegree_eq_finsum {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Proper (SchemeRealization.toBase X)]
    (α : cycleGroup (SchemeRealization.toBase X) (fun _ ↦ (0 : ℤ)) 0) :
    zeroCycleDegree α =
      ∑ᶠ x : Points X,
        (α : Function.locallyFinsupp (Points X) ℤ) x *
          (Module.finrank k (globalSectionsAlg (PointClosure.space x)) : ℤ) :=
  sorry

open scoped Classical in
/-- The singleton cycle of an integral closed subspace of relative dimension zero
belongs to the group of zero-cycles. -/
theorem mem_cycleGroup_single {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Proper (SchemeRealization.toBase X)]
    (Z : ClosedSubspace X) [IsIntegral Z.X]
    (hZ : closedSubspaceDeltaDimension (SchemeRealization.toBase X) (fun _ ↦ (0 : ℤ)) Z = (0 : EInt)) :
    locallyFinsuppWithin.single
        (Points.map Z.ι (ClosedSubspace.integralGenericPoint Z)) (1 : ℤ) ∈
      cycleGroup (SchemeRealization.toBase X) (fun _ ↦ (0 : ℤ)) 0 :=
  sorry

open scoped Classical in
/-- The degree of the singleton cycle of an integral zero-dimensional closed subspace
is the dimension of its global-sections algebra over the base field. -/
theorem zeroCycleDegree_single {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Proper (SchemeRealization.toBase X)]
    (Z : ClosedSubspace X) [IsIntegral Z.X]
    (hZ : closedSubspaceDeltaDimension (SchemeRealization.toBase X) (fun _ ↦ (0 : ℤ)) Z = (0 : EInt)) :
    zeroCycleDegree ⟨locallyFinsuppWithin.single
        (Points.map Z.ι (ClosedSubspace.integralGenericPoint Z)) (1 : ℤ),
      mem_cycleGroup_single Z hZ⟩ =
      (Module.finrank k (globalSectionsAlg Z.X) : ℤ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom

