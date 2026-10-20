module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.K0.Support.ChernCharacter

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/- Remark 42.56.11 (1): For `(S, δ)` as in Situation 42.7.1, `X` locally of finite type
over `S`, and a closed subscheme `Z ⊂ X`, if every irreducible component of `X` is
quasi-compact, localized Chern character induces a canonical additive and multiplicative
map `ch(Z ⟶ X, -) : K₀(D_{Z,perf}(O_X)) → ∏_{i≥0} Aⁱ(Z ⟶ X) ⊗ ℚ` sending a generator
`[E]` to `ch(Z ⟶ X, E)` and extending additively. -/
@[stacks 0FET] #check
  (AlgebraicGeometry.Scheme.K0WithSupport.canonicalChernCharacter :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      {X : Over S} [AlgebraicGeometry.LocallyOfFiniteType X.hom]
      {Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X.left)
      [AlgebraicGeometry.IsClosedImmersion i],
      (∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left)) →
        AlgebraicGeometry.Scheme.K0WithSupport X.left (Set.range i.base) →+
          AlgebraicGeometry.BivariantClass.Nonnegative.Rational.Completion δ
            (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X))

/- On a supported-perfect generator, the map is the localized Chern character
`ch(Z ⟶ X, E)`. -/
#check
  (AlgebraicGeometry.Scheme.K0WithSupport.canonicalChernCharacter_of :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      {X : Over S} [AlgebraicGeometry.LocallyOfFiniteType X.hom]
      {Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X.left)
      [AlgebraicGeometry.IsClosedImmersion i]
      (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
      (E : AlgebraicGeometry.RingedSpace.ModuleDerived.PerfectSupportedOn
        (Set.range i.base)),
      AlgebraicGeometry.Scheme.K0WithSupport.canonicalChernCharacter δ i hqc
          (TriangulatedK0.of E) =
        AlgebraicGeometry.Scheme.K0WithSupport.chernCharacterValue δ i hqc
          (AlgebraicGeometry.ChernClass.Theory.canonical δ X.hom) E)

/- Derived-tensor multiplication on supported-perfect `K₀` is sent to self-intersection
convolution of localized Chern characters. -/
#check
  (AlgebraicGeometry.Scheme.K0WithSupport.canonicalChernCharacter_mul :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      {X : Over S} [AlgebraicGeometry.LocallyOfFiniteType X.hom]
      {Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X.left)
      [AlgebraicGeometry.IsClosedImmersion i]
      (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
      (a b : AlgebraicGeometry.Scheme.K0WithSupport X.left (Set.range i.base)),
      AlgebraicGeometry.Scheme.K0WithSupport.canonicalChernCharacter δ i hqc (a * b) =
        AlgebraicGeometry.BivariantClass.Nonnegative.Rational.intersectionConvolution δ i
          (AlgebraicGeometry.Scheme.K0WithSupport.canonicalChernCharacter δ i hqc a)
          (AlgebraicGeometry.Scheme.K0WithSupport.canonicalChernCharacter δ i hqc b))

/- Remark 42.56.11 (2): If `X` is quasi-compact, the map `ch(Z ⟶ X, -)` has image
contained in `A^*(Z ⟶ X) ⊗ ℚ`. -/
@[stacks 0FET] #check
  (AlgebraicGeometry.Scheme.K0WithSupport.canonicalChernCharacter_finiteSupport :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      {X : Over S} [AlgebraicGeometry.LocallyOfFiniteType X.hom]
      {Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X.left)
      [AlgebraicGeometry.IsClosedImmersion i]
      (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
      (hX : CompactSpace X.left)
      (a : AlgebraicGeometry.Scheme.K0WithSupport X.left (Set.range i.base)),
      {p : ℕ | AlgebraicGeometry.Scheme.K0WithSupport.canonicalChernCharacter δ i hqc a p ≠
        0}.Finite)
