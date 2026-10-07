module

public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.ChernClass

@[expose] public section

open CategoryTheory
open scoped BigOperators

universe u

namespace AlgebraicGeometry.ChowGroup

variable {S X P : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
variable [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
variable [IsIntegral X] (E : X.Modules) (r : ℕ)
variable [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
variable (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
variable [LocallyOfFiniteType (π ≫ p)] (n : ℤ)
variable (hn : p.relativeDimensionFunction δ (genericPoint X) = n)
variable (F : ProjectiveBundleFormula δ p E r π hπ n hn)

/- The shared projective-bundle formula has the expected degree-specific data type. -/
#check (AlgebraicGeometry.ChowGroup.ProjectiveBundleFormula δ p E r π hπ n hn : Type u)

variable (pullbackThenC1PowerCap :
  (j : Fin (r + 1)) →
    @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance (n - (j : ℕ)) →+
      @ChowGroup P (LocallyOfFiniteType.isLocallyNoetherian (π ≫ p))
        ((π ≫ p).relativeDimensionFunction δ) inferInstance (n - 1))
variable (equiv :
  ((j : Fin r) →
    @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction δ) inferInstance (n - (j.succ : ℕ))) ≃+
    @ChowGroup P (LocallyOfFiniteType.isLocallyNoetherian (π ≫ p))
      ((π ≫ p).relativeDimensionFunction δ) inferInstance (n - 1))
variable (equiv_apply : ∀ a, equiv a =
  ∑ j : Fin r, pullbackThenC1PowerCap j.succ (a j))

/- The shared constructor rebuilds a projective-bundle formula from its observable data. -/
#check (AlgebraicGeometry.ChowGroup.ProjectiveBundleFormula.ofEquiv
    δ p E r π hπ n hn pullbackThenC1PowerCap equiv equiv_apply :
  ProjectiveBundleFormula δ p E r π hπ n hn)

/- Rebuilding a formula from its fields recovers that formula. -/
#check (AlgebraicGeometry.ChowGroup.ProjectiveBundleFormula.ofEquiv_eq
    δ p E r π hπ n hn F :
  ProjectiveBundleFormula.ofEquiv δ p E r π hπ n hn
      F.pullbackThenC1PowerCap F.equiv F.equiv_apply = F)

/- The shared construction returns the finite normalized Chern family. -/
#check (AlgebraicGeometry.ChowGroup.ProjectiveBundleFormula.chernClass
    δ p E r π hπ n hn F :
  (j : Fin (r + 1)) →
    @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction δ) inferInstance (n - (j : ℕ)))

/- The zeroth member of the shared Chern family is the fundamental Chow class. -/
#check (AlgebraicGeometry.ChowGroup.ProjectiveBundleFormula.chernClass_zero
    δ p E r π hπ n hn F :
  F.chernClass δ p E r π hπ n hn 0 =
    @chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction δ) inferInstance (n - (0 : ℕ))
      (@CycleGroup.fundamental X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) (n - (0 : ℕ))))

/- The abstract formula construction satisfies its signed relation. -/
#check (AlgebraicGeometry.ChowGroup.ProjectiveBundleFormula.chernClass_relation
    δ p E r π hπ n hn F :
  ∑ i : Fin (r + 1),
      (-1 : ℤ) ^ (i : ℕ) •
        F.pullbackThenC1PowerCap i.rev
          (F.chernClass δ p E r π hπ n hn i.rev) =
    0)

end AlgebraicGeometry.ChowGroup

namespace AlgebraicGeometry.ChowGroup.ProjectiveBundle

variable {S X P : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
variable [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
variable [IsIntegral X] (E : X.Modules) (r : ℕ)
variable [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
variable (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
variable (n : ℤ) (hn : p.relativeDimensionFunction δ (genericPoint X) = n)

/- The shared geometric term has the expected degree-indexed additive-map type. -/
#check (Formula.chernTerm δ p E r π hπ n :
  (j : Fin (r + 1)) →
    @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance (n - (j : ℕ)) →+
      Formula.totalSpaceChowGroup δ p E r π hπ (n - 1))

/- The positive geometric Chern map is bijective. -/
#check (Formula.positiveChernMap_bijective δ p E r π hπ n :
  Function.Bijective (Formula.positiveChernMap δ p E r π hπ n))

/- A represented finite-rank projective bundle has normalized Chern classes satisfying the
signed geometric relation. -/
#check (exists_chernClasses δ p E r π hπ n hn :
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
        0)

end AlgebraicGeometry.ChowGroup.ProjectiveBundle
