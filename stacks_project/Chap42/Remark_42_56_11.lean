/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import stacks_project.Chap42.Remark_42_56_11_ChernCharacter

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/- Remark 42.56.11 (1): For `(S, δ)` as in Situation 42.7.1, `X` locally of finite type
over `S`, and a closed subscheme `Z ⊂ X`, if every irreducible component of `X` is
quasi-compact, localized Chern character induces a canonical additive and multiplicative
map `ch(Z ⟶ X, -) : K₀(D_{Z,perf}(O_X)) → ∏_{i≥0} Aⁱ(Z ⟶ X) ⊗ ℚ` sending a generator
`[E]` to `ch(Z ⟶ X, E)` and extending additively. -/
@[stacks 0FET] #check
  (AlgebraicGeometry.Scheme.K0WithSupport.chernCharacter :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      {X : Over S} [AlgebraicGeometry.LocallyOfFiniteType X.hom]
      {Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X.left)
      [AlgebraicGeometry.IsClosedImmersion i],
      (∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left)) →
      AlgebraicGeometry.ChernClass.Theory δ X.hom →
        AlgebraicGeometry.Scheme.K0WithSupport X.left (Set.range i.base) →+
          AlgebraicGeometry.BivariantClass.Nonnegative.RationalCompletion δ
            (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))

/- On a supported-perfect generator, the map is the localized Chern character
`ch(Z ⟶ X, E)`. -/
#check
  (AlgebraicGeometry.Scheme.K0WithSupport.chernCharacter_of :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      {X : Over S} [AlgebraicGeometry.LocallyOfFiniteType X.hom]
      {Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X.left)
      [AlgebraicGeometry.IsClosedImmersion i]
      (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
      (classes : AlgebraicGeometry.ChernClass.Theory δ X.hom)
      (E : AlgebraicGeometry.RingedSpace.ModuleDerived.PerfectSupportedOn
        (Set.range i.base)),
      AlgebraicGeometry.Scheme.K0WithSupport.chernCharacter δ i hqc classes
          (TriangulatedK0.of E) =
        AlgebraicGeometry.Scheme.K0WithSupport.chernCharacterValue δ i hqc classes E)

/- Derived-tensor multiplication on supported-perfect `K₀` is sent to self-intersection
convolution of localized Chern characters. -/
#check
  (AlgebraicGeometry.Scheme.K0WithSupport.chernCharacter_mul :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      {X : Over S} [AlgebraicGeometry.LocallyOfFiniteType X.hom]
      {Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X.left)
      [AlgebraicGeometry.IsClosedImmersion i]
      (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
      (classes : AlgebraicGeometry.ChernClass.Theory δ X.hom)
      (a b : AlgebraicGeometry.Scheme.K0WithSupport X.left (Set.range i.base)),
      AlgebraicGeometry.Scheme.K0WithSupport.chernCharacter δ i hqc classes (a * b) =
        AlgebraicGeometry.Scheme.K0WithSupport.intersectionConvolution δ i
          (AlgebraicGeometry.Scheme.K0WithSupport.chernCharacter δ i hqc classes a)
          (AlgebraicGeometry.Scheme.K0WithSupport.chernCharacter δ i hqc classes b))

/- Remark 42.56.11 (2): If `X` is quasi-compact, the map `ch(Z ⟶ X, -)` has image
contained in `A^*(Z ⟶ X) ⊗ ℚ`. -/
@[stacks 0FET] #check
  (AlgebraicGeometry.Scheme.K0WithSupport.chernCharacter_finiteSupport :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      {X : Over S} [AlgebraicGeometry.LocallyOfFiniteType X.hom]
      {Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X.left)
      [AlgebraicGeometry.IsClosedImmersion i]
      (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
      (classes : AlgebraicGeometry.ChernClass.Theory δ X.hom)
      (hX : CompactSpace X.left)
      (a : AlgebraicGeometry.Scheme.K0WithSupport X.left (Set.range i.base)),
      {p : ℕ | AlgebraicGeometry.Scheme.K0WithSupport.chernCharacter δ i hqc classes a p ≠
        0}.Finite)
