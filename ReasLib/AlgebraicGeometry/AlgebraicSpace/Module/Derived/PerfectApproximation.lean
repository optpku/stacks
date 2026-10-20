module

public import Mathlib.Topology.Sets.Closeds
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Support

/-!
# Perfect approximation on algebraic spaces

A closed subset `T` of `Points X`, an object `E` of `DerivedQCoh X`, and an integer
`m` form a triple for which approximation holds when a perfect object of `D(𝒪_X)`
supported on `T` maps to `E` by a morphism that is a cohomology isomorphism in every
degree strictly above `m` and an epimorphism in degree `m`.

Perfectness is the library owner `AlgebraicSpace.ModuleDerived.IsPerfect` on `D(𝒪_X)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Approximation holds for a closed subset `T` of `Points X`, an object `E` of
`DerivedQCoh X`, and an integer `m` when some perfect object of `D(𝒪_X)` supported on
`T` maps to `E` by a morphism inducing cohomology isomorphisms in degrees `i` with
`m < i` and an epimorphism in degree `m`. -/
def HasPerfectApproximation {S : Scheme.{u}} {X : AlgebraicSpace S}
    (T : Closeds (Points X)) (E : DerivedQCoh X) (m : ℤ) : Prop :=
  ∃ P : ModuleDerived X,
    ModuleDerived.IsPerfect P ∧
      ModuleDerived.IsSupportedOn P T ∧
        ∃ α : P ⟶ E.obj,
          (∀ i : ℤ, m < i →
            IsIso ((DerivedCategory.homologyFunctor (Modules X) i).map α)) ∧
          Epi ((DerivedCategory.homologyFunctor (Modules X) m).map α)

/-- The existential characterization of a perfect approximation supported on a closed
subset. -/
theorem hasPerfectApproximation_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (T : Closeds (Points X)) (E : DerivedQCoh X) (m : ℤ) :
    HasPerfectApproximation T E m ↔
      ∃ P : ModuleDerived X,
        ModuleDerived.IsPerfect P ∧
          ModuleDerived.IsSupportedOn P T ∧
            ∃ α : P ⟶ E.obj,
              (∀ i : ℤ, m < i →
                IsIso ((DerivedCategory.homologyFunctor (Modules X) i).map α)) ∧
              Epi ((DerivedCategory.homologyFunctor (Modules X) m).map α) := sorry

namespace HasPerfectApproximation

/-- A perfect supported object and a cohomology isomorphism above `m` with an epimorphism
in degree `m` exhibit a perfect approximation. -/
theorem mk {S : Scheme.{u}} {X : AlgebraicSpace S}
    {T : Closeds (Points X)} {E : DerivedQCoh X} {m : ℤ} {P : ModuleDerived X}
    (hP : ModuleDerived.IsPerfect P) (hT : ModuleDerived.IsSupportedOn P T)
    (α : P ⟶ E.obj)
    (hiso : ∀ i : ℤ, m < i →
      IsIso ((DerivedCategory.homologyFunctor (Modules X) i).map α))
    (hepi : Epi ((DerivedCategory.homologyFunctor (Modules X) m).map α)) :
    HasPerfectApproximation T E m := sorry

/-- Perfect approximation is preserved when the quasi-coherent target is replaced by an
isomorphic derived object. -/
theorem of_iso {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Closeds (Points X)}
    {E F : DerivedQCoh X} {m : ℤ}
    (hE : HasPerfectApproximation T E m) (e : E ≅ F) :
    HasPerfectApproximation T F m := sorry

end HasPerfectApproximation

end AlgebraicGeometry.AlgebraicSpace
