/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import stacks_project.Chap42.Remark_42_56_10_Completion
import stacks_project.Chap42.Remark_42_56_10_ChernClass

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/- Remark 42.56.10: For `(S, δ)` as in Situation 42.7.1, `X` locally of finite type
over `S`, and a closed subscheme `Z ⊂ X`, if `X` is quasi-compact (or more generally
every irreducible component of `X` is quasi-compact), localized Chern classes induce
a canonical map `c(Z ⟶ X, -) : K₀(D_{Z,perf}(O_X)) → A⁰(X) × ∏_{i≥1} Aⁱ(Z ⟶ X)`
sending a generator `[E]` to `1 + c₁(Z ⟶ X, E) + c₂(Z ⟶ X, E) + ⋯` and extending
multiplicatively for the product of Remark 42.34.7. -/
@[stacks 0FES] #check
  (AlgebraicGeometry.Scheme.K0WithSupport.totalChernClass :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      {X : Over S} [AlgebraicGeometry.LocallyOfFiniteType X.hom]
      {Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X.left)
      [AlgebraicGeometry.IsClosedImmersion i],
      (CompactSpace X.left ∨
        ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left)) →
      AlgebraicGeometry.ChernClass.Theory δ X.hom →
        AlgebraicGeometry.Scheme.K0WithSupport X.left (Set.range i.base) →
          AlgebraicGeometry.BivariantClass.Cutoff.Family δ
            (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 1)

/- On a supported-perfect generator, the map is the mixed cutoff series
`1 + c₁(Z ⟶ X, E) + c₂(Z ⟶ X, E) + ⋯`. -/
#check
  (AlgebraicGeometry.Scheme.K0WithSupport.totalChernClass_of :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      {X : Over S} [AlgebraicGeometry.LocallyOfFiniteType X.hom]
      {Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X.left)
      [AlgebraicGeometry.IsClosedImmersion i]
      (hqc : CompactSpace X.left ∨
        ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
      (classes : AlgebraicGeometry.ChernClass.Theory δ X.hom)
      (E : AlgebraicGeometry.RingedSpace.ModuleDerived.PerfectSupportedOn
        (Set.range i.base)),
      AlgebraicGeometry.Scheme.K0WithSupport.totalChernClass δ i hqc classes
          (TriangulatedK0.of E) =
        AlgebraicGeometry.Scheme.K0WithSupport.totalChernValue δ i hqc classes E)

/- Addition in supported-perfect `K₀` is sent to convolution multiplication of
mixed total Chern classes. -/
#check
  (AlgebraicGeometry.Scheme.K0WithSupport.totalChernClass_add :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      {X : Over S} [AlgebraicGeometry.LocallyOfFiniteType X.hom]
      {Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X.left)
      [AlgebraicGeometry.IsClosedImmersion i]
      (hqc : CompactSpace X.left ∨
        ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
      (classes : AlgebraicGeometry.ChernClass.Theory δ X.hom)
      (a b : AlgebraicGeometry.Scheme.K0WithSupport X.left (Set.range i.base)),
      AlgebraicGeometry.Scheme.K0WithSupport.totalChernClass δ i hqc classes
          (a + b) =
        AlgebraicGeometry.Scheme.K0WithSupport.totalChernClass δ i hqc classes a *
          AlgebraicGeometry.Scheme.K0WithSupport.totalChernClass δ i hqc classes b)
