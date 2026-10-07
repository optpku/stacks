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

end AlgebraicGeometry.Scheme.Hom
