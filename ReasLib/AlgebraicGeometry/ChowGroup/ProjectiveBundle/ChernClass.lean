/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.Formula
public import ReasLib.AlgebraicGeometry.CycleGroup.Fundamental
public import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Chern classes from the projective-bundle formula

This file packages the degree-specific projective-bundle formula and uses its additive
equivalence to construct the normalized Chern classes in relative Chow groups.
-/

@[expose] public section

open CategoryTheory
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry

namespace ChowGroup

/-- Abstract degree-specific projective-bundle-formula data supplied as additive term maps
and an additive equivalence whose forward map is their finite sum. -/
structure ProjectiveBundleFormula
    {S X P : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    [IsIntegral X] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    [LocallyOfFiniteType (π ≫ p)] (n : ℤ)
    (hn : p.relativeDimensionFunction δ (genericPoint X) = n) where
  /-- The supplied additive term map for class index `j`. -/
  pullbackThenC1PowerCap :
    (j : Fin (r + 1)) →
      @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) inferInstance (n - (j : ℕ)) →+
        @ChowGroup P (LocallyOfFiniteType.isLocallyNoetherian (π ≫ p))
          ((π ≫ p).relativeDimensionFunction δ) inferInstance (n - 1)
  /-- The degree-`n - 1` projective-bundle-formula additive equivalence. -/
  equiv :
    ((j : Fin r) →
      @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance (n - (j.succ : ℕ))) ≃+
      @ChowGroup P (LocallyOfFiniteType.isLocallyNoetherian (π ≫ p))
        ((π ≫ p).relativeDimensionFunction δ) inferInstance (n - 1)
  /-- The forward equivalence is the sum of the supplied term maps. -/
  equiv_apply : ∀ a, equiv a =
    ∑ j : Fin r,
      pullbackThenC1PowerCap j.succ (a j)

namespace ProjectiveBundleFormula

/-- Build abstract projective-bundle-formula data from supplied term maps, an additive
equivalence, and its finite-sum specification. -/
def ofEquiv
    {S X P : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    [IsIntegral X] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    [LocallyOfFiniteType (π ≫ p)] (n : ℤ)
    (hn : p.relativeDimensionFunction δ (genericPoint X) = n)
    (pullbackThenC1PowerCap :
      (j : Fin (r + 1)) →
        @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
            (p.relativeDimensionFunction δ) inferInstance (n - (j : ℕ)) →+
          @ChowGroup P (LocallyOfFiniteType.isLocallyNoetherian (π ≫ p))
            ((π ≫ p).relativeDimensionFunction δ) inferInstance (n - 1))
    (equiv :
      ((j : Fin r) →
        @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) inferInstance (n - (j.succ : ℕ))) ≃+
        @ChowGroup P (LocallyOfFiniteType.isLocallyNoetherian (π ≫ p))
          ((π ≫ p).relativeDimensionFunction δ) inferInstance (n - 1))
    (equiv_apply : ∀ a, equiv a =
      ∑ j : Fin r,
        pullbackThenC1PowerCap j.succ (a j)) :
    ProjectiveBundleFormula δ p E r π hπ n hn :=
  ⟨pullbackThenC1PowerCap, equiv, equiv_apply⟩

/-- Rebuilding a projective-bundle formula from its maps, equivalence, and forward-map
specification recovers the original formula. -/
theorem ofEquiv_eq
    {S X P : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    [IsIntegral X] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    [LocallyOfFiniteType (π ≫ p)] (n : ℤ)
    (hn : p.relativeDimensionFunction δ (genericPoint X) = n)
    (F : ProjectiveBundleFormula δ p E r π hπ n hn) :
    ofEquiv δ p E r π hπ n hn F.pullbackThenC1PowerCap F.equiv F.equiv_apply = F := sorry

/-- The Chern classes determined by the projective-bundle formula, normalized in degree zero
by the Chow class of the fundamental cycle. -/
noncomputable def chernClass
    {S X P : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    [IsIntegral X] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    [LocallyOfFiniteType (π ≫ p)] (n : ℤ)
    (hn : p.relativeDimensionFunction δ (genericPoint X) = n)
    (F : ProjectiveBundleFormula δ p E r π hπ n hn) :
    (j : Fin (r + 1)) →
      @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance (n - (j : ℕ)) :=
  let c0 :=
    @chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction δ) inferInstance (n - (0 : ℕ))
      (@CycleGroup.fundamental X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) (n - (0 : ℕ)))
  let signedPositive := F.equiv.symm
    (-((-1 : ℤ) ^ r • F.pullbackThenC1PowerCap 0 c0))
  Fin.cases c0 (fun j ↦
    (-1 : ℤ) ^ ((j.succ : Fin (r + 1)).rev : ℕ) • signedPositive j)

/-- The zeroth Chern class determined by the projective-bundle formula is the Chow class of
the fundamental cycle of `X`. -/
theorem chernClass_zero
    {S X P : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    [IsIntegral X] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    [LocallyOfFiniteType (π ≫ p)] (n : ℤ)
    (hn : p.relativeDimensionFunction δ (genericPoint X) = n)
    (F : ProjectiveBundleFormula δ p E r π hπ n hn) :
    chernClass δ p E r π hπ n hn F 0 =
      @chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance (n - (0 : ℕ))
        (@CycleGroup.fundamental X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) (n - (0 : ℕ))) := sorry

/-- The alternating sum attached to supplied abstract projective-bundle-formula data vanishes
in degree `n - 1`. -/
theorem chernClass_relation
    {S X P : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    [IsIntegral X] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    [LocallyOfFiniteType (π ≫ p)] (n : ℤ)
    (hn : p.relativeDimensionFunction δ (genericPoint X) = n)
    (F : ProjectiveBundleFormula δ p E r π hπ n hn) :
    ∑ i : Fin (r + 1),
        (-1 : ℤ) ^ (i : ℕ) •
          F.pullbackThenC1PowerCap i.rev
            (F.chernClass δ p E r π hπ n hn i.rev) =
      0 := sorry

/-- A projective-bundle formula is geometric when each supplied term map agrees with the
canonical pullback and tautological first-Chern-cap term. -/
def IsGeometric
    {S X P : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    [IsIntegral X] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    [LocallyOfFiniteType (π ≫ p)] (n : ℤ)
    (hn : p.relativeDimensionFunction δ (genericPoint X) = n)
    (F : ProjectiveBundleFormula δ p E r π hπ n hn) : Prop :=
  ∀ j : Fin (r + 1),
    F.pullbackThenC1PowerCap j =
      ProjectiveBundle.Formula.chernTerm δ p E r π hπ n j

/-- Geometricity is equivalent to agreement of all formula terms with the canonical
projective-bundle Chern terms. -/
theorem isGeometric_iff
    {S X P : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    [IsIntegral X] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    [LocallyOfFiniteType (π ≫ p)] (n : ℤ)
    (hn : p.relativeDimensionFunction δ (genericPoint X) = n)
    (F : ProjectiveBundleFormula δ p E r π hπ n hn) :
    F.IsGeometric δ p E r π hπ n hn ↔
      ∀ j : Fin (r + 1),
        F.pullbackThenC1PowerCap j =
          ProjectiveBundle.Formula.chernTerm δ p E r π hπ n j := sorry

/-- The total Chern class determined by geometric projective-bundle-formula data, assembled
as the finite sum of its homogeneous classes in graded Chow homology. -/
noncomputable def totalChernClass
    {S X P : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    [IsIntegral X] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    [LocallyOfFiniteType (π ≫ p)] (n : ℤ)
    (hn : p.relativeDimensionFunction δ (genericPoint X) = n)
    (F : ProjectiveBundleFormula δ p E r π hπ n hn)
    (hF : F.IsGeometric δ p E r π hπ n hn) :
    DirectSum ℤ (fun k ↦
      @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k) :=
  ∑ i : Fin (r + 1),
    DirectSum.of _ (n - (i : ℕ)) (F.chernClass δ p E r π hπ n hn i)

/-- The degree `n - i` component of a total Chern class is its `i`-th homogeneous
Chern class. -/
theorem totalChernClass_component
    {S X P : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    [IsIntegral X] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    [LocallyOfFiniteType (π ≫ p)] (n : ℤ)
    (hn : p.relativeDimensionFunction δ (genericPoint X) = n)
    (F : ProjectiveBundleFormula δ p E r π hπ n hn)
    (hF : F.IsGeometric δ p E r π hπ n hn)
    (i : Fin (r + 1)) :
    totalChernClass δ p E r π hπ n hn F hF (n - (i : ℕ)) =
      F.chernClass δ p E r π hπ n hn i := sorry

/-- Two geometric projective-bundle formulae determine the same homogeneous Chern
classes. -/
theorem chernClass_eq_of_isGeometric
    {S X P : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    [IsIntegral X] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    [LocallyOfFiniteType (π ≫ p)] (n : ℤ)
    (hn : p.relativeDimensionFunction δ (genericPoint X) = n)
    (F G : ProjectiveBundleFormula δ p E r π hπ n hn)
    (hF : F.IsGeometric δ p E r π hπ n hn)
    (hG : G.IsGeometric δ p E r π hπ n hn) (i : Fin (r + 1)) :
    F.chernClass δ p E r π hπ n hn i =
      G.chernClass δ p E r π hπ n hn i := sorry

/-- The total Chern class is independent of the geometric projective-bundle-formula
presentation. -/
theorem totalChernClass_eq_of_isGeometric
    {S X P : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    [IsIntegral X] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    [LocallyOfFiniteType (π ≫ p)] (n : ℤ)
    (hn : p.relativeDimensionFunction δ (genericPoint X) = n)
    (F G : ProjectiveBundleFormula δ p E r π hπ n hn)
    (hF : F.IsGeometric δ p E r π hπ n hn)
    (hG : G.IsGeometric δ p E r π hπ n hn) :
    totalChernClass δ p E r π hπ n hn F hF =
      totalChernClass δ p E r π hπ n hn G hG := sorry

/-- The sign twist of an abstract projective-bundle-formula term. When the formula agrees
with the canonical geometric terms, this represents pullback followed by cap product with
the corresponding power of the dual tautological first Chern class. -/
noncomputable def dualC1PowerCap
    {S X P : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    [IsIntegral X] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    [LocallyOfFiniteType (π ≫ p)] (n : ℤ)
    (hn : p.relativeDimensionFunction δ (genericPoint X) = n)
    (F : ChowGroup.ProjectiveBundleFormula δ p E r π hπ n hn)
    (j : Fin (r + 1)) :
    @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) inferInstance (n - (j : ℕ)) →+
      @ChowGroup P (LocallyOfFiniteType.isLocallyNoetherian (π ≫ p))
        ((π ≫ p).relativeDimensionFunction δ) inferInstance (n - 1) :=
  (-1 : ℤ) ^ (j.rev : ℕ) • F.pullbackThenC1PowerCap j

/-- Applying `dualC1PowerCap` is the sign-twisted application of
`pullbackThenC1PowerCap`. -/
theorem dualC1PowerCap_apply
    {S X P : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    [IsIntegral X] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    [LocallyOfFiniteType (π ≫ p)] (n : ℤ)
    (hn : p.relativeDimensionFunction δ (genericPoint X) = n)
    (F : ChowGroup.ProjectiveBundleFormula δ p E r π hπ n hn)
    (j : Fin (r + 1))
    (α : @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction δ) inferInstance (n - (j : ℕ))) :
    dualC1PowerCap δ p E r π hπ n hn F j α =
      (-1 : ℤ) ^ (j.rev : ℕ) • F.pullbackThenC1PowerCap j α := sorry

end ProjectiveBundleFormula

namespace ProjectiveBundle.Formula

/-- The term in the projective-bundle Chern relation formed using the corresponding power
of the dual tautological first Chern class. -/
noncomputable def dualChernTerm
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (n : ℤ)
    (j : Fin (r + 1)) :
    @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance (n - (j : ℕ)) →+
      totalSpaceChowGroup δ p E r π hπ (n - 1) :=
  (-1 : ℤ) ^ (j.rev : ℕ) • Formula.chernTerm δ p E r π hπ n j

/-- Applying a dual Chern term is the sign-twisted application of the corresponding
tautological Chern term. -/
theorem dualChernTerm_apply
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (n : ℤ)
    (j : Fin (r + 1))
    (α : @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction δ) inferInstance (n - (j : ℕ))) :
    dualChernTerm δ p E r π hπ n j α =
      (-1 : ℤ) ^ (j.rev : ℕ) • Formula.chernTerm δ p E r π hπ n j α := sorry

end ProjectiveBundle.Formula

namespace ProjectiveBundle

/-- For a finite locally free module on an integral scheme, the represented projective
bundle determines normalized Chern classes whose signed projective-bundle relation vanishes. -/
theorem exists_chernClasses
    {S X P : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    [IsIntegral X] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    (n : ℤ) (hn : p.relativeDimensionFunction δ (genericPoint X) = n) :
    ∃ c : (j : Fin (r + 1)) →
        @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) inferInstance (n - (j : ℕ)),
      c 0 =
          @chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
            (p.relativeDimensionFunction δ) inferInstance (n - (0 : ℕ))
            (@CycleGroup.fundamental X (LocallyOfFiniteType.isLocallyNoetherian p)
              (p.relativeDimensionFunction δ) (n - (0 : ℕ))) ∧
        ∑ i : Fin (r + 1),
            (-1 : ℤ) ^ (i : ℕ) •
              Formula.chernTerm δ p E r π hπ n i.rev (c i.rev) =
          0 := sorry

/-- For a finite locally free module on an integral scheme, the represented projective
bundle determines normalized Chern classes whose dual-tautological relation vanishes. -/
theorem exists_chernClasses_dual_relation
    {S X P : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    [IsIntegral X] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    (n : ℤ) (hn : p.relativeDimensionFunction δ (genericPoint X) = n) :
    ∃ c : (j : Fin (r + 1)) →
        @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) inferInstance (n - (j : ℕ)),
      c 0 =
          @chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
            (p.relativeDimensionFunction δ) inferInstance (n - (0 : ℕ))
            (@CycleGroup.fundamental X (LocallyOfFiniteType.isLocallyNoetherian p)
              (p.relativeDimensionFunction δ) (n - (0 : ℕ))) ∧
        ∑ i : Fin (r + 1),
            Formula.dualChernTerm δ p E r π hπ n i.rev (c i.rev) =
          0 := sorry

end ProjectiveBundle

end ChowGroup

/-- If the abstract projective-bundle formula agrees with the canonical geometric terms,
the unsigned Chern-class relation formed with powers of the dual tautological first Chern
class vanishes. -/
theorem chernClass_projectiveBundle_dual_relation
    {S X P : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    [IsIntegral X] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    [LocallyOfFiniteType (π ≫ p)] (n : ℤ)
    (hn : p.relativeDimensionFunction δ (genericPoint X) = n)
    (F : ChowGroup.ProjectiveBundleFormula δ p E r π hπ n hn)
    (hF : ∀ j, F.pullbackThenC1PowerCap j =
      ChowGroup.ProjectiveBundle.Formula.chernTerm δ p E r π hπ n j) :
    ∑ i : Fin (r + 1),
        F.dualC1PowerCap δ p E r π hπ n hn i.rev
          (F.chernClass δ p E r π hπ n hn i.rev) =
      0 := sorry

end AlgebraicGeometry
