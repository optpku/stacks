module

public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.ChernClassCap
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.FormulaMap

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme.Hom
open scoped BigOperators

noncomputable section

namespace AlgebraicGeometry.ChowGroup

/-- The intrinsic values denoted by `c_j(E) ∩ α`, characterized by their zeroth
component, the projective-bundle relation, and vanishing above the rank of `E`. -/
structure ChernClassCap.{u}
    {S X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ)
    (alpha : CycleGroup X (p.relativeDimensionFunction delta) k) where
  component : (j : ℕ) →
    @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction delta) inferInstance (k - j)
  component_zero :
    component 0 = @reindex X (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction delta) inferInstance k (k - (0 : ℕ))
      (sub_zero k).symm
      (@chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction delta) inferInstance k alpha)
  projectiveBundleRelation :
    ∀ {P : Scheme.{u}} (pi : P ⟶ X)
      (hpi : Scheme.ProjectiveBundle.Representation pi E),
      match r, hE with
      | 0, hE =>
          @ProjectiveBundle.Formula.formulaMap S X P inferInstance delta inferInstance
            p inferInstance E 0 hE pi hpi k (fun i ↦ Fin.elim0 i) = 0
      | q + 1, hE =>
          ∑ i : Fin (q + 2),
            (-1 : ℤ) ^ (i : ℕ) •
              @reindex P
                (@LocallyOfFiniteType.isLocallyNoetherian _ _ (pi ≫ p)
                  (ProjectiveBundle.Formula.locallyOfFiniteTypeComp hpi p (q + 1)) inferInstance)
                (@Scheme.Hom.relativeDimensionFunction _ _ (pi ≫ p)
                  (ProjectiveBundle.Formula.locallyOfFiniteTypeComp hpi p (q + 1)) delta)
                (@instIsDimensionFunctionRelativeDimensionFunction _ _ (pi ≫ p)
                  inferInstance (ProjectiveBundle.Formula.locallyOfFiniteTypeComp hpi p (q + 1))
                  delta inferInstance)
                ((k - (i.rev : ℕ)) + (q : ℤ) - (i : ℕ)) (k - 1)
                (ProjectiveBundle.chernRelationGrade k q i)
                (@ProjectiveBundle.Formula.pullbackThenC1PowerCap S X P inferInstance delta
                  inferInstance p inferInstance E q hE pi hpi
                  (k - (i.rev : ℕ)) (i : ℕ) (component (i.rev : ℕ))) = 0
  component_eq_zero : ∀ j : ℕ, r < j → component j = 0

universe u

namespace ChernClassCap

/-- Build a Chern-class cap from its explicit components and their characterizing laws. -/
def ofComponents
    {S X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ)
    (alpha : CycleGroup X (p.relativeDimensionFunction delta) k)
    (component : (j : ℕ) →
      @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction delta) inferInstance (k - j))
    (component_zero :
      component 0 = @reindex X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction delta) inferInstance k (k - (0 : ℕ))
        (sub_zero k).symm
        (@chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction delta) inferInstance k alpha))
    (projectiveBundleRelation :
      ∀ {P : Scheme.{u}} (pi : P ⟶ X)
        (hpi : Scheme.ProjectiveBundle.Representation pi E),
        match r, hE with
        | 0, hE =>
            @ProjectiveBundle.Formula.formulaMap S X P inferInstance delta inferInstance
              p inferInstance E 0 hE pi hpi k (fun i ↦ Fin.elim0 i) = 0
        | q + 1, hE =>
            ∑ i : Fin (q + 2),
              (-1 : ℤ) ^ (i : ℕ) •
                @reindex P
                  (@LocallyOfFiniteType.isLocallyNoetherian _ _ (pi ≫ p)
                    (ProjectiveBundle.Formula.locallyOfFiniteTypeComp hpi p (q + 1)) inferInstance)
                  (@Scheme.Hom.relativeDimensionFunction _ _ (pi ≫ p)
                    (ProjectiveBundle.Formula.locallyOfFiniteTypeComp hpi p (q + 1)) delta)
                  (@instIsDimensionFunctionRelativeDimensionFunction _ _ (pi ≫ p)
                    inferInstance (ProjectiveBundle.Formula.locallyOfFiniteTypeComp hpi p (q + 1))
                    delta inferInstance)
                  ((k - (i.rev : ℕ)) + (q : ℤ) - (i : ℕ)) (k - 1)
                  (ProjectiveBundle.chernRelationGrade k q i)
                  (@ProjectiveBundle.Formula.pullbackThenC1PowerCap S X P inferInstance delta
                    inferInstance p inferInstance E q hE pi hpi
                    (k - (i.rev : ℕ)) (i : ℕ) (component (i.rev : ℕ))) = 0)
    (component_eq_zero : ∀ j : ℕ, r < j → component j = 0) :
    ChernClassCap delta p E r k alpha :=
  { component := component
    component_zero := component_zero
    projectiveBundleRelation := projectiveBundleRelation
    component_eq_zero := component_eq_zero }

/-- The component family satisfies normalization, every projective-bundle relation,
and vanishing above the rank. -/
theorem spec
    {S X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ)
    (alpha : CycleGroup X (p.relativeDimensionFunction delta) k)
    (c : ChernClassCap delta p E r k alpha) :
    c.component 0 = @reindex X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction delta) inferInstance k (k - (0 : ℕ))
        (sub_zero k).symm
        (@chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction delta) inferInstance k alpha) ∧
      (∀ {P : Scheme.{u}} (pi : P ⟶ X)
        (hpi : Scheme.ProjectiveBundle.Representation pi E),
        match r, hE with
        | 0, hE =>
            @ProjectiveBundle.Formula.formulaMap S X P inferInstance delta inferInstance
              p inferInstance E 0 hE pi hpi k (fun i ↦ Fin.elim0 i) = 0
        | q + 1, hE =>
            ∑ i : Fin (q + 2),
              (-1 : ℤ) ^ (i : ℕ) •
                @reindex P
                  (@LocallyOfFiniteType.isLocallyNoetherian _ _ (pi ≫ p)
                    (ProjectiveBundle.Formula.locallyOfFiniteTypeComp hpi p (q + 1)) inferInstance)
                  (@Scheme.Hom.relativeDimensionFunction _ _ (pi ≫ p)
                    (ProjectiveBundle.Formula.locallyOfFiniteTypeComp hpi p (q + 1)) delta)
                  (@instIsDimensionFunctionRelativeDimensionFunction _ _ (pi ≫ p)
                    inferInstance (ProjectiveBundle.Formula.locallyOfFiniteTypeComp hpi p (q + 1))
                    delta inferInstance)
                  ((k - (i.rev : ℕ)) + (q : ℤ) - (i : ℕ)) (k - 1)
                  (ProjectiveBundle.chernRelationGrade k q i)
                  (@ProjectiveBundle.Formula.pullbackThenC1PowerCap S X P inferInstance delta
                    inferInstance p inferInstance E q hE pi hpi
                    (k - (i.rev : ℕ)) (i : ℕ) (c.component (i.rev : ℕ))) = 0) ∧
      ∀ j : ℕ, r < j → c.component j = 0 := sorry

/-- Chern-class caps satisfying the intrinsic projective-bundle characterization exist. -/
theorem nonempty
    {S X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ)
    (alpha : CycleGroup X (p.relativeDimensionFunction delta) k) :
    Nonempty (ChernClassCap delta p E r k alpha) := sorry

/-- The intrinsic characterization makes the Chern-class cap independent of its realization. -/
theorem unique
    {S X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (k : ℤ)
    (alpha : CycleGroup X (p.relativeDimensionFunction delta) k)
    (c d : ChernClassCap delta p E r k alpha) :
    c = d := sorry

end ChernClassCap

end AlgebraicGeometry.ChowGroup
