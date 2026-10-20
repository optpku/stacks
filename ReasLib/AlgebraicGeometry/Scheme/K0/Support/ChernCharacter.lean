module

public import ReasLib.AlgebraicGeometry.Scheme.K0.Support.Ring
public import ReasLib.CategoryTheory.Pretriangulated.K0.Universal
public import ReasLib.AlgebraicGeometry.LocalizedChern.Classes
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Canonical
public import ReasLib.AlgebraicGeometry.BivariantClass.Nonnegative.Intersection

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open AlgebraicGeometry.LocalizedChern
open AlgebraicGeometry.BivariantClass.Nonnegative

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.K0WithSupport

variable {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
variable {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
variable (i : Z ⟶ X.left) [IsClosedImmersion i]

/-- Quasi-compactness of every irreducible component of `X`, together with support on `Z`,
produces a vanishing-mode localized-Chern situation. -/
theorem characterSituation
    (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) :
    Situation S δ X i E.obj 0 .vanishing := sorry

/-- The localized Chern character of a supported perfect complex, as a completed rational
bivariant class of `Z ⟶ X`. -/
def chernCharacterValue
    (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) :
    Rational.Completion δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) :=
  rationalCharacter i classes E.obj (characterSituation δ i hqc E).perfect
    (characterSituation δ i hqc E).offCenter
    (characterSituation δ i hqc E).finiteness

/-- A coefficient of the generator-level localized Chern character is the corresponding
localized character component. -/
theorem chernCharacterValue_apply
    (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) (p : ℕ) :
    chernCharacterValue δ i hqc classes E p =
      rationalCharacter i classes E.obj (characterSituation δ i hqc E).perfect
        (characterSituation δ i hqc E).offCenter
        (characterSituation δ i hqc E).finiteness p := rfl

/-- Localized Chern characters of supported perfect complexes add on distinguished
triangles. -/
theorem chernCharacterValue_distinguished
    (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom)
    (T : Triangle (RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base))) :
    chernCharacterValue δ i hqc classes T.obj₂ =
      chernCharacterValue δ i hqc classes T.obj₁ +
        chernCharacterValue δ i hqc classes T.obj₃ := sorry

/-- The additive localized Chern character on supported-perfect `K₀`. -/
def chernCharacterWithTheory
    (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom) :
    K0WithSupport X.left (Set.range i.base) →+
      Rational.Completion δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) :=
  TriangulatedK0.liftOfDistinguished (chernCharacterValue δ i hqc classes)
    (chernCharacterValue_distinguished δ i hqc classes)

/-- The bundled localized Chern character sends a supported-perfect generator to its
localized character. -/
theorem chernCharacterWithTheory_of
    (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) :
    chernCharacterWithTheory δ i hqc classes (TriangulatedK0.of E) =
      chernCharacterValue δ i hqc classes E :=
  TriangulatedK0.liftOfDistinguished_of (chernCharacterValue δ i hqc classes)
    (chernCharacterValue_distinguished δ i hqc classes) E

/-- The zero class maps to the zero completed rational bivariant class. -/
theorem chernCharacterWithTheory_zero
    (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom) :
    chernCharacterWithTheory δ i hqc classes 0 = 0 :=
  (chernCharacterWithTheory δ i hqc classes).map_zero

/-- Derived-tensor multiplication on supported-perfect `K₀` is sent to self-intersection
convolution of localized Chern characters. -/
theorem chernCharacterWithTheory_mul
    (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom)
    (a b : K0WithSupport X.left (Set.range i.base)) :
    chernCharacterWithTheory δ i hqc classes (a * b) =
      Rational.intersectionConvolution δ i (chernCharacterWithTheory δ i hqc classes a)
        (chernCharacterWithTheory δ i hqc classes b) := sorry

/-- If `X` is quasi-compact, the localized Chern character of a supported-perfect class
has only finitely many nonzero homogeneous components. -/
theorem chernCharacterWithTheory_finiteSupport
    (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom) (hX : CompactSpace X.left)
    (a : K0WithSupport X.left (Set.range i.base)) :
    {p : ℕ | chernCharacterWithTheory δ i hqc classes a p ≠ 0}.Finite := sorry

/-- The canonical additive localized Chern character on supported-perfect K-theory. -/
def canonicalChernCharacter
    (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left)) :
    K0WithSupport X.left (Set.range i.base) →+
      Rational.Completion δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) :=
  chernCharacterWithTheory δ i hqc (ChernClass.Theory.canonical δ X.hom)

/-- The canonical character of a supported-perfect generator is its localized character. -/
theorem canonicalChernCharacter_of
    (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) :
    canonicalChernCharacter δ i hqc (TriangulatedK0.of E) =
      chernCharacterValue δ i hqc (ChernClass.Theory.canonical δ X.hom) E :=
  chernCharacterWithTheory_of δ i hqc (ChernClass.Theory.canonical δ X.hom) E

/-- The canonical localized Chern character preserves derived-tensor multiplication. -/
theorem canonicalChernCharacter_mul
    (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (a b : K0WithSupport X.left (Set.range i.base)) :
    canonicalChernCharacter δ i hqc (a * b) =
      Rational.intersectionConvolution δ i (canonicalChernCharacter δ i hqc a)
        (canonicalChernCharacter δ i hqc b) :=
  chernCharacterWithTheory_mul δ i hqc (ChernClass.Theory.canonical δ X.hom) a b

/-- On a quasi-compact ambient scheme the canonical character has finite homogeneous support. -/
theorem canonicalChernCharacter_finiteSupport
    (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (hX : CompactSpace X.left) (a : K0WithSupport X.left (Set.range i.base)) :
    {p : ℕ | canonicalChernCharacter δ i hqc a p ≠ 0}.Finite :=
  chernCharacterWithTheory_finiteSupport δ i hqc (ChernClass.Theory.canonical δ X.hom) hX a

end AlgebraicGeometry.Scheme.K0WithSupport
