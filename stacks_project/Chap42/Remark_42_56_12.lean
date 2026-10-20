module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.K0.Support.Universal
import ReasLib.AlgebraicGeometry.Scheme.K0.DerivedChernClass
import ReasLib.AlgebraicGeometry.Scheme.K0.DerivedChernCharacter

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/- Remark 42.56.12 (1): With Z = X, every perfect complex is supported on X, so
`K₀(D_{Z,perf}(O_X)) = K₀(D_perf(O_X)) = K₀(X)`. -/
@[stacks 0FEU] #check
  (AlgebraicGeometry.Scheme.K0WithSupport.equivK0 :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      AlgebraicGeometry.Scheme.K0WithSupport X Set.univ ≃+
        AlgebraicGeometry.Scheme.K0 X)

/- Remark 42.56.12 (2): For `(S, δ)` as in Situation 42.7.1 and `X` locally of finite type
over `S`, if `X` is quasi-compact (or every irreducible component of `X` is quasi-compact),
derived total Chern classes induce `c : K₀(X) → ∏ Aⁱ(X)`. -/
@[stacks 0FEU] #check
  (AlgebraicGeometry.Scheme.K0.totalChernClass :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [AlgebraicGeometry.UniversallyCatenary S] [IsDimensionFunction δ]
      [AlgebraicGeometry.LocallyOfFiniteType p],
      (CompactSpace X ∨
        ∀ C : irreducibleComponents X, IsCompact (C : Set X)) →
      AlgebraicGeometry.ChernClass.Theory δ p →
        AlgebraicGeometry.Scheme.K0 X →
          AlgebraicGeometry.ChowCohomology.Nonnegative.Completion δ p)

/- On a perfect-complex generator, the map is the derived total Chern class. -/
#check
  (AlgebraicGeometry.Scheme.K0.totalChernClass_of :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [AlgebraicGeometry.UniversallyCatenary S] [IsDimensionFunction δ]
      [AlgebraicGeometry.LocallyOfFiniteType p]
      (hqc : CompactSpace X ∨
        ∀ C : irreducibleComponents X, IsCompact (C : Set X))
      (classes : AlgebraicGeometry.ChernClass.Theory δ p)
      (E : AlgebraicGeometry.RingedSpace.ModuleDerived.Perfect),
      AlgebraicGeometry.Scheme.K0.totalChernClass δ p hqc classes
          (TriangulatedK0.of E) =
        AlgebraicGeometry.Scheme.K0.totalChernValue δ p hqc classes E)

/- Remark 42.56.12 (3): Under the same hypotheses, derived Chern characters induce a
ring homomorphism `ch : K₀(X) → ∏ Aⁱ(X) ⊗ ℚ`. -/
@[stacks 0FEU] #check
  (AlgebraicGeometry.Scheme.K0.chernCharacter :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [AlgebraicGeometry.UniversallyCatenary S] [IsDimensionFunction δ]
      [AlgebraicGeometry.LocallyOfFiniteType p],
      (CompactSpace X ∨
        ∀ C : irreducibleComponents X, IsCompact (C : Set X)) →
      AlgebraicGeometry.ChernClass.Theory δ p →
        AlgebraicGeometry.Scheme.K0 X →+*
          AlgebraicGeometry.ChowCohomology.Nonnegative.RationalCompletion δ p)

/- On a perfect-complex generator, the ring homomorphism is the derived Chern character. -/
#check
  (AlgebraicGeometry.Scheme.K0.chernCharacter_of :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [AlgebraicGeometry.UniversallyCatenary S] [IsDimensionFunction δ]
      [AlgebraicGeometry.LocallyOfFiniteType p]
      (hqc : CompactSpace X ∨
        ∀ C : irreducibleComponents X, IsCompact (C : Set X))
      (classes : AlgebraicGeometry.ChernClass.Theory δ p)
      (E : AlgebraicGeometry.RingedSpace.ModuleDerived.Perfect),
      AlgebraicGeometry.Scheme.K0.chernCharacter δ p hqc classes
          (TriangulatedK0.of E) =
        AlgebraicGeometry.Scheme.K0.chernCharacterValue δ p hqc classes E)

/- The canonical map `K₀(Vect(X)) → K₀(X)` sending a finite locally free module to itself
as a perfect complex in degree 0. -/
#check
  (AlgebraicGeometry.Scheme.VectorBundleK0.toK0RingHom :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      AlgebraicGeometry.Scheme.VectorBundleK0 X →+*
        AlgebraicGeometry.Scheme.K0 X)

/- Remark 42.56.12 (4): The diagram relating vector-bundle and perfect-complex total Chern
classes commutes. -/
@[stacks 0FEU] #check
  (AlgebraicGeometry.Scheme.K0.totalChernClass_comp_toK0 :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [AlgebraicGeometry.UniversallyCatenary S] [IsDimensionFunction δ]
      [AlgebraicGeometry.LocallyOfFiniteType p]
      (hqc : CompactSpace X ∨
        ∀ C : irreducibleComponents X, IsCompact (C : Set X))
      (classes : AlgebraicGeometry.ChernClass.Theory δ p)
      (a : AlgebraicGeometry.Scheme.VectorBundleK0 X),
      AlgebraicGeometry.Scheme.K0.totalChernClass δ p hqc classes
          (AlgebraicGeometry.Scheme.VectorBundleK0.toK0 X a) =
        AlgebraicGeometry.Scheme.VectorBundleK0.totalChernClass δ p classes a)

/- Remark 42.56.12 (5): The diagram relating vector-bundle and perfect-complex Chern
characters commutes. -/
@[stacks 0FEU] #check
  (AlgebraicGeometry.Scheme.K0.chernCharacter_comp_toK0 :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [AlgebraicGeometry.UniversallyCatenary S] [IsDimensionFunction δ]
      [AlgebraicGeometry.LocallyOfFiniteType p]
      (hqc : CompactSpace X ∨
        ∀ C : irreducibleComponents X, IsCompact (C : Set X))
      (classes : AlgebraicGeometry.ChernClass.Theory δ p)
      (a : AlgebraicGeometry.Scheme.VectorBundleK0 X),
      AlgebraicGeometry.Scheme.K0.chernCharacter δ p hqc classes
          (AlgebraicGeometry.Scheme.VectorBundleK0.toK0 X a) =
        AlgebraicGeometry.Scheme.VectorBundleK0.chernCharacter δ p classes a)
