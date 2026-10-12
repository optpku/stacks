/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.Support
public import stacks_project.Chap42.Remark_42_52_3_CutoffChern
public import stacks_project.Chap42.Remark_42_56_10_Completion

/-!
# Localized total Chern classes on supported-perfect `K₀`

The mixed cutoff series of Remark 42.52.3 at bound `1` is the generator value
of a multiplicative map out of `K₀(D_{Z,perf}(O_X))`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.BivariantClass.Cutoff
open AlgebraicGeometry.BivariantClass.Cutoff.Family
open AlgebraicGeometry.LocalizedChern

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.K0WithSupport

/-- Quasi-compactness of `X`, or of every irreducible component of `X`, together with
support on `Z`, produces a rank-bound localized-Chern situation of bound `1`. -/
theorem situation_ofSupported
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) :
    Situation S δ X i E.obj 1 .rankBound := sorry

/-- The mixed cutoff series of a supported perfect complex, as a family in
`A⁰(X) × ∏_{i≥1} Aⁱ(Z ⟶ X)`. -/
def totalChernValue
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) :
    Family δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 1 :=
  mixedChernClass i classes E.obj 1 (situation_ofSupported δ i hqc E)

/-- A coefficient of the mixed total Chern-class value is the corresponding mixed
cutoff class. -/
theorem totalChernValue_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) (n : ℕ) :
    totalChernValue δ i hqc classes E n =
      mixedChernClass i classes E.obj 1 (situation_ofSupported δ i hqc E) n :=
  sorry

/-- The constant coefficient of a mixed total Chern-class value is the identity class
of `X`. -/
theorem totalChernValue_zero
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) :
    totalChernValue δ i hqc classes E 0 =
      one δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 0 := sorry

/-- Every mixed total Chern-class value is central in the source cutoff family. -/
theorem totalChernValue_mem_center
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) :
    totalChernValue δ i hqc classes E ∈
      Set.center (Family δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 1) := sorry

/-- Package a mixed total Chern-class value as a unit of the center of the cutoff family. -/
def totalChernUnitValue
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) :
    (Submonoid.center
      (Family δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 1))ˣ :=
  unitOf δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
    (totalChernValue δ i hqc classes E)
    (totalChernValue_zero δ i hqc classes E)
    (totalChernValue_mem_center δ i hqc classes E)

/-- The underlying cutoff family of `totalChernUnitValue` is `totalChernValue`. -/
theorem totalChernUnitValue_val
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) :
    (totalChernUnitValue δ i hqc classes E).val.val =
      totalChernValue δ i hqc classes E := sorry

/-- Distinguished-triangle relations lie in the kernel of the free additive lift of
the unit-valued mixed total Chern class. -/
theorem relations_le_ker_totalChernClass
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom) :
    TriangulatedK0.relations
        (RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) ≤
      (FreeAbelianGroup.lift fun E :
          RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base) ↦
        Additive.ofMul (totalChernUnitValue δ i hqc classes E)).ker := sorry

/-- The mixed total Chern class as an additive homomorphism into the additive group of
units of the cutoff family. -/
def totalChernClassHom
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom) :
    K0WithSupport X.left (Set.range i.base) →+
      Additive ((Submonoid.center
        (Family δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 1))ˣ) :=
  TriangulatedK0.lift
    (fun E ↦ Additive.ofMul (totalChernUnitValue δ i hqc classes E))
    (relations_le_ker_totalChernClass δ i hqc classes)

/-- The bundled mixed total Chern-class map takes a generator to its packaged mixed
series. -/
theorem totalChernClassHom_of
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) :
    totalChernClassHom δ i hqc classes (TriangulatedK0.of E) =
      Additive.ofMul (totalChernUnitValue δ i hqc classes E) := sorry

/-- The product-valued mixed total Chern-class map obtained by forgetting unit
packaging. -/
def totalChernClass
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom)
    (a : K0WithSupport X.left (Set.range i.base)) :
    Family δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 1 :=
  (totalChernClassHom δ i hqc classes a).toMul.val.val

/-- A supported-perfect generator maps to its mixed cutoff series. -/
theorem totalChernClass_of
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) :
    totalChernClass δ i hqc classes (TriangulatedK0.of E) =
      totalChernValue δ i hqc classes E := sorry

/-- On a supported-perfect generator, the degree-zero coefficient is the identity
class of `X` and every positive-degree coefficient is the corresponding localized
Chern class. -/
theorem totalChernClass_apply_of
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) (n : ℕ) :
    totalChernClass δ i hqc classes (TriangulatedK0.of E) n =
      mixedChernClass i classes E.obj 1 (situation_ofSupported δ i hqc E) n :=
  sorry

/-- The zero class maps to the convolution unit. -/
theorem totalChernClass_zero
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom) :
    totalChernClass δ i hqc classes 0 = 1 := sorry

/-- Addition in supported-perfect `K₀` becomes convolution multiplication of mixed
total Chern classes. -/
theorem totalChernClass_add
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom)
    (a b : K0WithSupport X.left (Set.range i.base)) :
    totalChernClass δ i hqc classes (a + b) =
      totalChernClass δ i hqc classes a *
        totalChernClass δ i hqc classes b := sorry

/-- Negation in supported-perfect `K₀` becomes formal inversion of mixed total Chern
classes. -/
theorem totalChernClass_neg
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom)
    (a : K0WithSupport X.left (Set.range i.base)) :
    totalChernClass δ i hqc classes (-a) =
      formalInverse δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
        (totalChernClass δ i hqc classes a) := sorry

end AlgebraicGeometry.Scheme.K0WithSupport
