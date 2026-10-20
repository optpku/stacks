/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.ChernClass
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.Definedness
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.Triangulated

/-!
# Total Chern classes on perfect `K₀`

When a scheme or each of its irreducible components is quasi-compact, derived
total Chern classes descend through triangle relations to a multiplicative map
`K0 X → Completion δ p`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.K0

variable {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)

/-- For `X` locally of finite type over a universally catenary scheme `S` with
dimension function `δ`, quasi-compactness of `X`, or of every irreducible component
of `X`, makes Chern classes of every perfect complex defined. -/
theorem isDefined_of_hqc
    (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (E : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :
    ChernClass.Derived.IsDefined E.obj := sorry

variable [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]

/-- The completed total Chern-class value of a perfect complex. -/
def totalChernValue
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (classes : ChernClass.Theory δ p)
    (E : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :
    ChowCohomology.Nonnegative.Completion δ p :=
  ChernClass.Derived.totalClass δ p classes E.obj E.property (isDefined_of_hqc δ p hqc E)

/-- A coefficient of the completed total Chern-class value is the corresponding
derived Chern-class component. -/
theorem totalChernValue_apply
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (classes : ChernClass.Theory δ p)
    (E : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) (i : ℕ) :
    totalChernValue δ p hqc classes E i =
      ChernClass.Derived.totalClass δ p classes E.obj E.property
        (isDefined_of_hqc δ p hqc E) i := sorry

/-- The constant coefficient of a total Chern-class value is one. -/
theorem totalChernValue_zero
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (classes : ChernClass.Theory δ p)
    (E : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :
    totalChernValue δ p hqc classes E 0 = ChowCohomology.one δ p := sorry

/-- Every total Chern-class value is central in the completed Chow ring. -/
theorem totalChernValue_mem_center
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (classes : ChernClass.Theory δ p)
    (E : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :
    totalChernValue δ p hqc classes E ∈
      Set.center (ChowCohomology.Nonnegative.Completion δ p) := sorry

/-- Package a total Chern-class value as a unit of the center of the completed Chow ring. -/
def totalChernUnitValue
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (classes : ChernClass.Theory δ p)
    (E : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :
    (Submonoid.center (ChowCohomology.Nonnegative.Completion δ p))ˣ :=
  ChowCohomology.Nonnegative.Completion.unitOf δ p
    (totalChernValue δ p hqc classes E)
    (totalChernValue_zero δ p hqc classes E)
    (totalChernValue_mem_center δ p hqc classes E)

/-- The underlying completed class of `totalChernUnitValue` is `totalChernValue`. -/
theorem totalChernUnitValue_val
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (classes : ChernClass.Theory δ p)
    (E : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :
    (totalChernUnitValue δ p hqc classes E).val.val =
      totalChernValue δ p hqc classes E := sorry

/-- Distinguished-triangle relations lie in the kernel of the free additive lift of the
central-unit-valued total Chern class. -/
theorem relations_le_ker_totalChernClass
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (classes : ChernClass.Theory δ p) :
    TriangulatedK0.relations (RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) ≤
      (FreeAbelianGroup.lift fun E : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace) ↦
        Additive.ofMul (totalChernUnitValue δ p hqc classes E)).ker := sorry

/-- The total Chern class as an additive homomorphism into the additive form of
the commutative group of central units. -/
def totalChernClassHom
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (classes : ChernClass.Theory δ p) :
    K0 X →+
      Additive ((Submonoid.center (ChowCohomology.Nonnegative.Completion δ p))ˣ) :=
  TriangulatedK0.lift
    (fun E ↦ Additive.ofMul (totalChernUnitValue δ p hqc classes E))
    (relations_le_ker_totalChernClass δ p hqc classes)

/-- The bundled total Chern-class map takes a generator to its packaged total class. -/
theorem totalChernClassHom_of
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (classes : ChernClass.Theory δ p)
    (E : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :
    totalChernClassHom δ p hqc classes (TriangulatedK0.of E) =
      Additive.ofMul (totalChernUnitValue δ p hqc classes E) := sorry

/-- The product-valued total Chern-class map obtained by forgetting the central-unit packaging. -/
def totalChernClass
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (classes : ChernClass.Theory δ p) (a : K0 X) :
    ChowCohomology.Nonnegative.Completion δ p :=
  (totalChernClassHom δ p hqc classes a).toMul.val.val

/-- A perfect-complex generator maps to its completed total Chern-class value. -/
theorem totalChernClass_of
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (classes : ChernClass.Theory δ p)
    (E : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :
    totalChernClass δ p hqc classes (TriangulatedK0.of E) =
      totalChernValue δ p hqc classes E := sorry

/-- The zero class maps to the convolution unit. -/
theorem totalChernClass_zero
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (classes : ChernClass.Theory δ p) :
    totalChernClass δ p hqc classes 0 = 1 := sorry

/-- Addition in perfect `K₀` becomes convolution multiplication of total Chern classes. -/
theorem totalChernClass_add
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (classes : ChernClass.Theory δ p) (a b : K0 X) :
    totalChernClass δ p hqc classes (a + b) =
      totalChernClass δ p hqc classes a * totalChernClass δ p hqc classes b := sorry

/-- The total Chern class of a finite locally free module, placed in degree zero, recovers
the vector-bundle total Chern class. -/
theorem totalChernClass_comp_toK0
    (hqc : CompactSpace X ∨ ∀ C : irreducibleComponents X, IsCompact (C : Set X))
    (classes : ChernClass.Theory δ p) (a : VectorBundleK0 X) :
    totalChernClass δ p hqc classes (VectorBundleK0.toK0 X a) =
      VectorBundleK0.totalChernClass δ p classes a := sorry

end AlgebraicGeometry.Scheme.K0
