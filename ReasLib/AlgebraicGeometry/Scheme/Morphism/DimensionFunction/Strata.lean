/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay.DimensionFunction
public import ReasLib.AlgebraicGeometry.Scheme.Normal
import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Dimension
import ReasLib.AlgebraicGeometry.Scheme.Normal.Components.LocallyNoetherian
import ReasLib.Topology.IrreducibleComponents
import ReasLib.Topology.Specialization.Dimension.Catenary

/-!
# Generic relative-dimension strata

This file relates global clopen strata for a relative dimension function to its local behavior at
generic points and records two standard sufficient conditions for such strata to exist.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A decomposition into clopen strata on which the generic relative dimension is constant. -/
structure GenericDimensionStratification {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ] where
  /-- The clopen stratum of generic relative dimension `n`. -/
  stratum : ℤ → X.Opens
  /-- The strata cover the source scheme. -/
  iSup_stratum : iSup stratum = ⊤
  /-- Distinct strata are disjoint. -/
  pairwise_disjoint :
    Pairwise (fun m n ↦ Disjoint (stratum m : Set X) (stratum n : Set X))
  /-- Every stratum is also closed. -/
  isClopen_stratum : ∀ n, IsClopen (stratum n : Set X)
  /-- Generic points in the `n`-th stratum have relative dimension `n`. -/
  relativeDimension_eq : ∀ n ξ, ξ ∈ (stratum n).genericPointsInAmbient →
    f.relativeDimensionFunction δ ξ = n

namespace GenericDimensionStratification

/-- Construct a generic-dimension stratification from an explicit family of clopen strata. -/
def ofStrata {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ]
    (U : ℤ → X.Opens) (cover : iSup U = ⊤)
    (disjoint : Pairwise (fun m n ↦ Disjoint (U m : Set X) (U n : Set X)))
    (clopen : ∀ n, IsClopen (U n : Set X))
    (dimension : ∀ n ξ, ξ ∈ (U n).genericPointsInAmbient →
      f.relativeDimensionFunction δ ξ = n) :
    f.GenericDimensionStratification δ where
  stratum := U
  iSup_stratum := cover
  pairwise_disjoint := disjoint
  isClopen_stratum := clopen
  relativeDimension_eq := dimension

/-- The strata of a stratification built by `ofStrata` are the supplied family. -/
@[simp]
theorem ofStrata_stratum {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ]
    (U : ℤ → X.Opens) (cover : iSup U = ⊤)
    (disjoint : Pairwise (fun m n ↦ Disjoint (U m : Set X) (U n : Set X)))
    (clopen : ∀ n, IsClopen (U n : Set X))
    (dimension : ∀ n ξ, ξ ∈ (U n).genericPointsInAmbient →
      f.relativeDimensionFunction δ ξ = n) :
    (ofStrata f δ U cover disjoint clopen dimension).stratum = U := sorry

/-- The covering, disjointness, clopenness, and dimension laws of a stratification. -/
theorem spec {X S : Scheme.{u}} {f : X ⟶ S}
    [UniversallyCatenary S] [LocallyOfFiniteType f] {δ : S → ℤ} [IsDimensionFunction δ]
    (D : f.GenericDimensionStratification δ) :
    iSup D.stratum = ⊤ ∧
      Pairwise (fun m n ↦ Disjoint (D.stratum m : Set X) (D.stratum n : Set X)) ∧
      (∀ n, IsClopen (D.stratum n : Set X)) ∧
      ∀ n ξ, ξ ∈ (D.stratum n).genericPointsInAmbient →
        f.relativeDimensionFunction δ ξ = n := sorry

end GenericDimensionStratification

/-- The global clopen decomposition, local-open-neighbourhood, and
component-through-a-point descriptions of generic relative-dimension strata are equivalent. -/
theorem genericDimensionStrata_tfae {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ] :
    List.TFAE
      [ ∃ U : ℤ → X.Opens,
          iSup U = ⊤ ∧
            Pairwise (fun m n ↦ Disjoint (U m : Set X) (U n : Set X)) ∧
            (∀ n, IsClopen (U n : Set X)) ∧
            ∀ n ξ, ξ ∈ (U n).genericPointsInAmbient →
              f.relativeDimensionFunction δ ξ = n
      , ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
          ∃ n : ℤ, ∀ ξ, ξ ∈ U.genericPointsInAmbient →
            f.relativeDimensionFunction δ ξ = n
      , ∀ x : X, ∃ n : ℤ, ∀ ξ : genericPoints X,
          x ∈ (genericPoints.component ξ : Set X) →
            f.relativeDimensionFunction δ ξ.1 = n
      ] := sorry

/-- A normal scheme has a clopen decomposition by its generic relative-dimension strata. -/
theorem existsGenericDimensionStrata_of_isNormal {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ]
    (hX : X.isNormal) :
    ∃ U : ℤ → X.Opens,
      iSup U = ⊤ ∧
        Pairwise (fun m n ↦ Disjoint (U m : Set X) (U n : Set X)) ∧
        (∀ n, IsClopen (U n : Set X)) ∧
        ∀ n ξ, ξ ∈ (U n).genericPointsInAmbient →
          f.relativeDimensionFunction δ ξ = n := sorry

/-- A Cohen–Macaulay scheme has a clopen decomposition by its generic relative-dimension
strata. -/
theorem existsGenericDimensionStrata_of_cohenMacaulay {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ]
    [Scheme.CohenMacaulay X] :
    ∃ U : ℤ → X.Opens,
      iSup U = ⊤ ∧
        Pairwise (fun m n ↦ Disjoint (U m : Set X) (U n : Set X)) ∧
        (∀ n, IsClopen (U n : Set X)) ∧
        ∀ n ξ, ξ ∈ (U n).genericPointsInAmbient →
          f.relativeDimensionFunction δ ξ = n := sorry

/-- An integer is a generic-dimension index at a point when every irreducible component
through that point has that generic relative dimension. -/
def IsGenericDimensionIndex {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (x : X) (n : ℤ) : Prop :=
  ∀ ξ : genericPoints X, x ∈ (genericPoints.component ξ : Set X) →
    f.relativeDimensionFunction δ ξ.1 = n

/-- A generic-dimension index specifies the relative dimension of every generic point of
an irreducible component through the given point. -/
theorem isGenericDimensionIndex_iff {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (x : X) (n : ℤ) :
    IsGenericDimensionIndex f δ x n ↔
      ∀ ξ : genericPoints X, x ∈ (genericPoints.component ξ : Set X) →
        f.relativeDimensionFunction δ ξ.1 = n := Iff.rfl

/-- A generic-dimension index of a point, when it exists, is unique. -/
theorem isGenericDimensionIndex_unique {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (x : X) {n m : ℤ}
    (hn : IsGenericDimensionIndex f δ x n)
    (hm : IsGenericDimensionIndex f δ x m) : n = m := sorry

/-- The open generic-dimension index locus is the interior of the points with that index. -/
def genericDimensionIndexLocus {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (n : ℤ) : X.Opens :=
  ⟨interior {x | IsGenericDimensionIndex f δ x n}, isOpen_interior⟩

/-- If a generic-dimension index exists at every point, the index loci are disjoint clopen
strata covering the scheme, with the specified generic dimensions and index membership. -/
theorem genericDimensionIndexLoci_spec {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h : ∀ x : X, ∃ n, IsGenericDimensionIndex f δ x n) :
    iSup (genericDimensionIndexLocus f δ) = ⊤ ∧
      Pairwise (fun m n ↦ Disjoint
        (genericDimensionIndexLocus f δ m : Set X)
        (genericDimensionIndexLocus f δ n : Set X)) ∧
      (∀ n, IsClopen (genericDimensionIndexLocus f δ n : Set X)) ∧
      (∀ n ξ, ξ ∈ (genericDimensionIndexLocus f δ n).genericPointsInAmbient →
        f.relativeDimensionFunction δ ξ = n) ∧
      ∀ (x : X) (n : ℤ), x ∈ genericDimensionIndexLocus f δ n ↔
        IsGenericDimensionIndex f δ x n := sorry

namespace GenericDimensionStratification

/-- The canonical generic-dimension stratification uses the interiors of the index loci. -/
def ofPointwise {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h : ∀ x : X, ∃ n, IsGenericDimensionIndex f δ x n) :
    f.GenericDimensionStratification δ :=
  ofStrata f δ (genericDimensionIndexLocus f δ)
    (genericDimensionIndexLoci_spec f δ h).1
    (genericDimensionIndexLoci_spec f δ h).2.1
    (genericDimensionIndexLoci_spec f δ h).2.2.1
    (genericDimensionIndexLoci_spec f δ h).2.2.2.1

/-- Membership in the canonical generic-dimension stratum is the index condition. -/
theorem mem_ofPointwise {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h : ∀ x : X, ∃ n, IsGenericDimensionIndex f δ x n) (x : X) (n : ℤ) :
    x ∈ (ofPointwise f δ h).stratum n ↔ IsGenericDimensionIndex f δ x n :=
  (genericDimensionIndexLoci_spec f δ h).2.2.2.2 x n

end GenericDimensionStratification

end AlgebraicGeometry.Scheme.Hom
