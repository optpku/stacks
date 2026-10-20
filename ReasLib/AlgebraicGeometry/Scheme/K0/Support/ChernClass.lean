/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.Support
public import ReasLib.AlgebraicGeometry.LocalizedChern.Mixed
public import ReasLib.AlgebraicGeometry.BivariantClass.Cutoff.Completion
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Canonical

/-!
# Localized total Chern classes on supported-perfect `K₀`

The canonical mixed cutoff series at bound `1` gives a multiplicative map
from the triangulated Grothendieck group of supported perfect complexes
to ambient degree-zero and positive localized bivariant classes.
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

/-- The canonical mixed cutoff series of a supported perfect complex, as a family in
`A⁰(X) × ∏_{i≥1} Aⁱ(Z ⟶ X)`. -/
def totalChernValue
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) :
    Family δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 1 :=
  mixedChernClass i (ChernClass.Theory.canonical δ X.hom) E.obj 1 (situation_ofSupported δ i hqc E)

/-- A coefficient of the mixed total Chern-class value is the corresponding mixed
cutoff class. -/
theorem totalChernValue_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) (n : ℕ) :
    totalChernValue δ i hqc E n =
      mixedChernClass i (ChernClass.Theory.canonical δ X.hom) E.obj 1 (situation_ofSupported δ i hqc E) n :=
  sorry

/-- The constant coefficient of a mixed total Chern-class value is the identity class
of `X`. -/
theorem totalChernValue_zero
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) :
    totalChernValue δ i hqc E 0 =
      one δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 0 := sorry

/-- Every canonical mixed total Chern-class value is central in the cutoff family. -/
theorem totalChernValue_mem_center
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) :
    totalChernValue δ i hqc E ∈
      Set.center (Family δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 1) := sorry

/-- Package a mixed total Chern-class value as a unit of the center of the cutoff family. -/
def totalChernUnitValue
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) :
    (Submonoid.center
      (Family δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 1))ˣ :=
  unitOf δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
    (totalChernValue δ i hqc E)
    (totalChernValue_zero δ i hqc E)
    (totalChernValue_mem_center δ i hqc E)

/-- The underlying cutoff family of `totalChernUnitValue` is `totalChernValue`. -/
theorem totalChernUnitValue_val
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) :
    (totalChernUnitValue δ i hqc E).val.val =
      totalChernValue δ i hqc E := sorry

/-- Distinguished-triangle relations lie in the kernel of the free additive lift of
the unit-valued mixed total Chern class. -/
theorem relations_le_ker_totalChernClass
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left)) :
    TriangulatedK0.relations
        (RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) ≤
      (FreeAbelianGroup.lift fun E :
          RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base) ↦
        Additive.ofMul (totalChernUnitValue δ i hqc E)).ker := sorry

/-- The canonical mixed total Chern class as an additive homomorphism into the
additive group of units of the center of the cutoff family. -/
def totalChernClassHom
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left)) :
    K0WithSupport X.left (Set.range i.base) →+
      Additive ((Submonoid.center
        (Family δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 1))ˣ) :=
  TriangulatedK0.lift
    (fun E ↦ Additive.ofMul (totalChernUnitValue δ i hqc E))
    (relations_le_ker_totalChernClass δ i hqc)

/-- The bundled mixed total Chern-class map takes a generator to its packaged mixed
series. -/
theorem totalChernClassHom_of
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) :
    totalChernClassHom δ i hqc (TriangulatedK0.of E) =
      Additive.ofMul (totalChernUnitValue δ i hqc E) := sorry

/-- The canonical total localized Chern-class map to the product of ambient degree-zero
and positive localized bivariant classes, obtained by forgetting unit packaging. -/
def totalChernClass
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (a : K0WithSupport X.left (Set.range i.base)) :
    Family δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 1 :=
  (totalChernClassHom δ i hqc a).toMul.val.val

/-- A supported-perfect generator maps to its mixed cutoff series. -/
theorem totalChernClass_of
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) :
    totalChernClass δ i hqc (TriangulatedK0.of E) =
      totalChernValue δ i hqc E := sorry

/-- On a supported-perfect generator, the degree-zero coefficient is the identity
class of `X` and every positive-degree coefficient is the corresponding localized
Chern class. -/
theorem totalChernClass_apply_of
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) (n : ℕ) :
    totalChernClass δ i hqc (TriangulatedK0.of E) n =
      mixedChernClass i (ChernClass.Theory.canonical δ X.hom) E.obj 1 (situation_ofSupported δ i hqc E) n :=
  sorry

/-- The zero class maps to the convolution unit. -/
theorem totalChernClass_zero
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left)) :
    totalChernClass δ i hqc 0 = 1 := sorry

/-- Addition in supported-perfect `K₀` becomes convolution multiplication of mixed
total Chern classes. -/
theorem totalChernClass_add
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (a b : K0WithSupport X.left (Set.range i.base)) :
    totalChernClass δ i hqc (a + b) =
      totalChernClass δ i hqc a *
        totalChernClass δ i hqc b := sorry

/-- Negation in supported-perfect `K₀` becomes formal inversion of mixed total Chern
classes. -/
theorem totalChernClass_neg
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (hqc : CompactSpace X.left ∨
      ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (a : K0WithSupport X.left (Set.range i.base)) :
    totalChernClass δ i hqc (-a) =
      formalInverse δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
        (totalChernClass δ i hqc a) := sorry

end AlgebraicGeometry.Scheme.K0WithSupport
