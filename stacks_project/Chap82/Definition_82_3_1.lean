module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.ClosedSubspace
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace

section

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ] (k : ℤ)

/- Definition 82.3.1: In Situation 82.2.1, for good `X / B`, a cycle is an
integer formal combination of integral closed subspaces with locally finite
nonzero supports. Points index integral closed subspaces by their generic
points; their supports are the closures of these singleton points. A `k`-cycle
has nonzero coefficient only on subspaces of `δ`-dimension `k`, and these cycles
form the abelian group `Z_k(X)` under coefficientwise operations. -/
@[stacks 0EDZ] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.mem_cycleGroup_iff_closedSubspaceDeltaDimension :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ] (k : ℤ)
      (α : Function.locallyFinsupp (Points X) ℤ),
      α ∈ AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup f δ k ↔
      ∀ (Z : ClosedSubspace X) (hZ : IsIntegral Z.X) (ξ : Points X),
        IsGenericPoint ξ Z.pointsSet → α ξ ≠ 0 →
          AlgebraicGeometry.AlgebraicSpace.Hom.closedSubspaceDeltaDimension f δ Z = (k : EInt))

/- Unrestricted cycles permit infinitely many integer coefficients, subject only
to local finiteness (Topology, Definition 5.28.4). -/
#check (Function.locallyFinsupp (Points X) ℤ : Type (u + 1))

/- Local finiteness applies to the integral closed supports, namely singleton
closures of generic points with nonzero coefficient. -/
#check (AlgebraicGeometry.AlgebraicSpace.locallyFinite_support_closures :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (α : Function.locallyFinsupp (Points X) ℤ),
    LocallyFinite fun x : α.support ↦ closure ({x.val} : Set (Points X)))

/- In Situation 82.2.1, the abelian group of all
`k`-cycles on `X` is `Z_k(X) = AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup f δ k`. -/
#check (AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} (f : X ⟶ B) [LocallyOfFiniteType f]
    (δ : Points B → ℤ) (k : ℤ),
    AddSubgroup (Function.locallyFinsupp (Points X) ℤ))

/- A function belonging to the locally supported additive subgroup determines
a function with locally finite support within the prescribed subset. -/
#check (Function.locallyFinsuppWithin.mk_of_mem_addSubgroup :
  ∀ {T : Type v} [TopologicalSpace T] {U : Set T} {A : Type w} [AddGroup A]
    (g : T → A) (hg : g ∈ Function.locallyFinsuppWithin.addSubgroup U),
    Function.locallyFinsuppWithin U A)

/- Singleton cycles supply coefficient generators, indexed geometrically by
integral closed supports through their generic points. -/
#check (Function.locallyFinsuppWithin.single :
  ∀ {T : Type v} [TopologicalSpace T] {A : Type w} [DecidableEq T] [Zero A],
    T → A → Function.locallyFinsupp T A)

/- The singleton cycle has its specified coefficient at its indexing point
and zero coefficient at every other point. -/
#check (Function.locallyFinsuppWithin.single_apply :
  ∀ {T : Type v} [TopologicalSpace T] {A : Type w} [DecidableEq T] [Zero A]
    {x₁ x₂ : T} {y : A},
    Function.locallyFinsuppWithin.single x₁ y x₂ = if x₂ = x₁ then y else 0)

end

end AlgebraicGeometry.AlgebraicSpace
