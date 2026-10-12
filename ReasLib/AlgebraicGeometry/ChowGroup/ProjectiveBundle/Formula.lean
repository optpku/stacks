/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.CycleGroup.Reindex
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Basic
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# The projective-bundle formula on Chow groups

This file defines flat pullback to a represented projective bundle, intersection with the
first Chern class of its tautological module, and the finite sum occurring in the
projective-bundle formula.
-/

@[expose] public section

open CategoryTheory
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.ProjectiveBundle.Formula

/-- A projective bundle of a finite locally free module, followed by a locally finite type
morphism, is locally of finite type. -/
theorem locallyOfFiniteTypeComp
    {S X P : Scheme.{u}} {E : X.Modules} {π : P ⟶ X}
    (hπ : Scheme.ProjectiveBundle.Representation π E) (p : X ⟶ S) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] [LocallyOfFiniteType p] :
    LocallyOfFiniteType (π ≫ p) := sorry

/-- A represented projective bundle of a rank-`q + 1` finite locally free module is flat. -/
theorem flat
    {X P : Scheme.{u}} {E : X.Modules} {π : P ⟶ X}
    (hπ : Scheme.ProjectiveBundle.Representation π E) (q : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank (q + 1) E] : Flat π := sorry

/-- A represented projective bundle of a rank-`q + 1` finite locally free module has
relative dimension `q`. -/
theorem relativeDimension
    {X P : Scheme.{u}} {E : X.Modules} {π : P ⟶ X}
    (hπ : Scheme.ProjectiveBundle.Representation π E) (q : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank (q + 1) E] :
    Scheme.Hom.RelativeDimension π q := sorry

/-- The Chow group of the total space of a represented finite-rank projective bundle. -/
abbrev totalSpaceChowGroup
    {S X P : Scheme.{u}} (δ : S → ℤ) [UniversallyCatenary S] [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (k : ℤ) : Type u :=
  @ChowGroup P
    (@LocallyOfFiniteType.isLocallyNoetherian _ _ (π ≫ p)
      (locallyOfFiniteTypeComp hπ p r) inferInstance)
    ((π ≫ p).relativeDimensionFunction δ)
    (@Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction _ _ (π ≫ p)
      inferInstance (locallyOfFiniteTypeComp hπ p r) δ inferInstance) k

/-- Flat pullback to a positive-rank represented projective bundle sends rational boundaries
to rational boundaries. -/
theorem flatPullback_mem_boundaries
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (q : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank (q + 1) E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (k : ℤ) :
    @RationalEquivalence.boundaries X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k ≤
      (@RationalEquivalence.boundaries P
        (@LocallyOfFiniteType.isLocallyNoetherian _ _ (π ≫ p)
          (locallyOfFiniteTypeComp hπ p (q + 1)) inferInstance)
        ((π ≫ p).relativeDimensionFunction δ)
        (@Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction _ _ (π ≫ p)
          inferInstance (locallyOfFiniteTypeComp hπ p (q + 1)) δ inferInstance)
        (k + (q : ℤ))).comap
        (@CycleGroup.flatPullback S inferInstance δ inferInstance
          (Over.mk (π ≫ p)) (Over.mk p)
          (locallyOfFiniteTypeComp hπ p (q + 1))
          (inferInstanceAs (LocallyOfFiniteType p))
          (Over.homMk π) q (@flat X P E π hπ q inferInstance)
          (@relativeDimension X P E π hπ q inferInstance) k) := sorry

/-- Flat pullback from the base to a positive-rank represented projective bundle on relative
Chow groups. -/
noncomputable def flatPullback
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (q : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank (q + 1) E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (k : ℤ) :
    @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k →+
      totalSpaceChowGroup δ p E (q + 1) π hπ (k + (q : ℤ)) :=
  QuotientAddGroup.map
    (@RationalEquivalence.boundaries X (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction δ) inferInstance k)
    (@RationalEquivalence.boundaries P
      (@LocallyOfFiniteType.isLocallyNoetherian _ _ (π ≫ p)
        (locallyOfFiniteTypeComp hπ p (q + 1)) inferInstance)
      ((π ≫ p).relativeDimensionFunction δ)
      (@Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction _ _ (π ≫ p)
        inferInstance (locallyOfFiniteTypeComp hπ p (q + 1)) δ inferInstance)
      (k + (q : ℤ)))
    (@CycleGroup.flatPullback S inferInstance δ inferInstance
      (Over.mk (π ≫ p)) (Over.mk p)
      (locallyOfFiniteTypeComp hπ p (q + 1))
      (inferInstanceAs (LocallyOfFiniteType p))
      (Over.homMk π) q (@flat X P E π hπ q inferInstance)
      (@relativeDimension X P E π hπ q inferInstance) k)
    (flatPullback_mem_boundaries δ p E q π hπ k)

/-- Projective-bundle flat pullback is computed on cycle representatives by cycle flat
pullback followed by passage to the Chow class. -/
theorem flatPullback_chowClass
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (q : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank (q + 1) E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (k : ℤ)
    (α : CycleGroup X (p.relativeDimensionFunction δ) k) :
    flatPullback δ p E q π hπ k
        (@chowClass X (LocallyOfFiniteType.isLocallyNoetherian p)
          (p.relativeDimensionFunction δ) inferInstance k α) =
      @chowClass P
        (@LocallyOfFiniteType.isLocallyNoetherian _ _ (π ≫ p)
          (locallyOfFiniteTypeComp hπ p (q + 1)) inferInstance)
        ((π ≫ p).relativeDimensionFunction δ)
        (@Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction _ _ (π ≫ p)
          inferInstance (locallyOfFiniteTypeComp hπ p (q + 1)) δ inferInstance)
        (k + (q : ℤ))
        (@CycleGroup.flatPullback S inferInstance δ inferInstance
          (Over.mk (π ≫ p)) (Over.mk p)
          (locallyOfFiniteTypeComp hπ p (q + 1))
          (inferInstanceAs (LocallyOfFiniteType p))
          (Over.homMk π) q (@flat X P E π hπ q inferInstance)
          (@relativeDimension X P E π hπ q inferInstance) k α) := sorry

/-- Rational boundaries on a projective-bundle total space lie in the kernel of the
tautological first-Chern cap map. -/
theorem firstChernClassCap_mem_ker
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (k : ℤ) :
    @RationalEquivalence.boundaries P
        (@LocallyOfFiniteType.isLocallyNoetherian _ _ (π ≫ p)
          (locallyOfFiniteTypeComp hπ p r) inferInstance)
        ((π ≫ p).relativeDimensionFunction δ)
        (@Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction _ _ (π ≫ p)
          inferInstance (locallyOfFiniteTypeComp hπ p r) δ inferInstance) k ≤
      ((@Scheme.Modules.firstChernClassCap S P (π ≫ p) inferInstance
          (locallyOfFiniteTypeComp hπ p r) δ inferInstance
          (Scheme.ProjectiveBundle.tautologicalSheaf π hπ)
          (Scheme.ProjectiveBundle.tautologicalSheaf_isInvertible π hπ) (k - 1)).comp
        (CycleGroup.reindex ((π ≫ p).relativeDimensionFunction δ)
          (sub_add_cancel k 1).symm)).ker := sorry

/-- Intersection with the first Chern class of the tautological module on a represented
projective bundle. -/
noncomputable def firstChernClassCap
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (k : ℤ) :
    totalSpaceChowGroup δ p E r π hπ k →+
      totalSpaceChowGroup δ p E r π hπ (k - 1) :=
  QuotientAddGroup.lift
    (@RationalEquivalence.boundaries P
      (@LocallyOfFiniteType.isLocallyNoetherian _ _ (π ≫ p)
        (locallyOfFiniteTypeComp hπ p r) inferInstance)
      ((π ≫ p).relativeDimensionFunction δ)
      (@Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction _ _ (π ≫ p)
        inferInstance (locallyOfFiniteTypeComp hπ p r) δ inferInstance) k)
    ((@Scheme.Modules.firstChernClassCap S P (π ≫ p) inferInstance
      (locallyOfFiniteTypeComp hπ p r) δ inferInstance
      (Scheme.ProjectiveBundle.tautologicalSheaf π hπ)
      (Scheme.ProjectiveBundle.tautologicalSheaf_isInvertible π hπ) (k - 1)).comp
      (CycleGroup.reindex ((π ≫ p).relativeDimensionFunction δ)
        (sub_add_cancel k 1).symm))
    (firstChernClassCap_mem_ker δ p E r π hπ k)

/-- Tautological first-Chern cap on the Chow group is computed by the corresponding
cycle-level operation on a representative. -/
theorem firstChernClassCap_chowClass
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (k : ℤ)
    (α : CycleGroup P ((π ≫ p).relativeDimensionFunction δ) k) :
    firstChernClassCap δ p E r π hπ k
        (@chowClass P
          (@LocallyOfFiniteType.isLocallyNoetherian _ _ (π ≫ p)
            (locallyOfFiniteTypeComp hπ p r) inferInstance)
          ((π ≫ p).relativeDimensionFunction δ)
          (@Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction _ _ (π ≫ p)
            inferInstance (locallyOfFiniteTypeComp hπ p r) δ inferInstance) k α) =
      @Scheme.Modules.firstChernClassCap S P (π ≫ p) inferInstance
        (locallyOfFiniteTypeComp hπ p r) δ inferInstance
        (Scheme.ProjectiveBundle.tautologicalSheaf π hπ)
        (Scheme.ProjectiveBundle.tautologicalSheaf_isInvertible π hπ) (k - 1)
        (CycleGroup.reindex ((π ≫ p).relativeDimensionFunction δ)
          (sub_add_cancel k 1).symm α) := sorry

/-- Transport a projective-bundle total-space Chow group along an equality of degrees. -/
noncomputable def reindex
    {S X P : Scheme.{u}} (δ : S → ℤ) [UniversallyCatenary S] [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    {a b : ℤ} (h : a = b) :
    totalSpaceChowGroup δ p E r π hπ a ≃+
      totalSpaceChowGroup δ p E r π hπ b :=
  AddEquiv.cast (M := fun k : ℤ ↦ totalSpaceChowGroup δ p E r π hπ k) h

/-- Transporting a projective-bundle total-space Chow group along reflexivity is the
identity additive equivalence. -/
theorem reindex_refl
    {S X P : Scheme.{u}} (δ : S → ℤ) [UniversallyCatenary S] [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (a : ℤ) :
    reindex δ p E r π hπ (rfl : a = a) =
      AddEquiv.refl (totalSpaceChowGroup δ p E r π hπ a) := sorry

/-- The grading after one more tautological first-Chern cap agrees with subtraction by the
successor. -/
theorem c1PowerCap_succ_grade (k : ℤ) (s : ℕ) :
    (k - (s : ℤ)) - 1 = k - ((s + 1 : ℕ) : ℤ) := sorry

/-- Repeated intersection with the first Chern class of the tautological module on a
represented projective bundle. -/
noncomputable def c1PowerCap
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    (k : ℤ) (s : ℕ) :
    totalSpaceChowGroup δ p E r π hπ k →+
      totalSpaceChowGroup δ p E r π hπ (k - (s : ℤ)) :=
  Nat.rec
    (reindex δ p E r π hπ (sub_zero k).symm).toAddMonoidHom
    (fun s cap ↦
      (reindex δ p E r π hπ (c1PowerCap_succ_grade k s)).toAddMonoidHom.comp
        ((firstChernClassCap δ p E r π hπ (k - (s : ℤ))).comp cap))
    s

/-- The zeroth tautological first-Chern power cap is the canonical degree transport. -/
theorem c1PowerCap_zero
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (k : ℤ) :
    c1PowerCap δ p E r π hπ k 0 =
      (reindex δ p E r π hπ (sub_zero k).symm).toAddMonoidHom := sorry

/-- The successor tautological first-Chern power cap is one further cap followed by the
canonical grading transport. -/
theorem c1PowerCap_succ
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    (k : ℤ) (s : ℕ) :
    c1PowerCap δ p E r π hπ k (s + 1) =
      (reindex δ p E r π hπ (c1PowerCap_succ_grade k s)).toAddMonoidHom.comp
        ((firstChernClassCap δ p E r π hπ (k - (s : ℤ))).comp
          (c1PowerCap δ p E r π hπ k s)) := sorry

/-- Pullback to a positive-rank represented projective bundle followed by a specified power
of the tautological first-Chern cap. -/
noncomputable def pullbackThenC1PowerCap
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (q : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank (q + 1) E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    (k : ℤ) (s : ℕ) :
    @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance k →+
      totalSpaceChowGroup δ p E (q + 1) π hπ (k + (q : ℤ) - (s : ℤ)) :=
  (c1PowerCap δ p E (q + 1) π hπ (k + (q : ℤ)) s).comp
    (flatPullback δ p E q π hπ k)

/-- Evaluating pullback followed by a tautological Chern power is evaluation of the two
composed additive maps. -/
theorem pullbackThenC1PowerCap_apply
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (q : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank (q + 1) E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    (k : ℤ) (s : ℕ)
    (α : @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction δ) inferInstance k) :
    pullbackThenC1PowerCap δ p E q π hπ k s α =
      c1PowerCap δ p E (q + 1) π hπ (k + (q : ℤ)) s
        (flatPullback δ p E q π hπ k α) := sorry

/-- The degree of the term indexed by `j` in the Chern relation is `n - 1`. -/
theorem chernTerm_grade (n : ℤ) (q : ℕ) (j : Fin (q + 2)) :
    (n - (j : ℕ)) + (q : ℤ) - (j.rev : ℕ) = n - 1 := sorry

/-- The Chern-relation term indexed by `j`: pullback followed by the `j.rev`-th power of
the tautological first-Chern cap, with the rank-zero case given by the zero map. -/
noncomputable def chernTerm
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (n : ℤ)
    (j : Fin (r + 1)) :
    @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance (n - (j : ℕ)) →+
      totalSpaceChowGroup δ p E r π hπ (n - 1) :=
  match r, j, hE with
  | 0, _, _ => 0
  | q + 1, j, _ =>
      (reindex δ p E (q + 1) π hπ (chernTerm_grade n q j)).toAddMonoidHom.comp
        (pullbackThenC1PowerCap δ p E q π hπ (n - (j : ℕ)) (j.rev : ℕ))

/-- In positive rank, evaluating a Chern-relation term is pullback followed by the indexed
tautological first-Chern power and the canonical degree transport. -/
theorem chernTerm_apply
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (q : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank (q + 1) E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (n : ℤ)
    (j : Fin (q + 2))
    (α : @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction δ) inferInstance (n - (j : ℕ))) :
    chernTerm δ p E (q + 1) π hπ n j α =
      reindex δ p E (q + 1) π hπ (chernTerm_grade n q j)
        (pullbackThenC1PowerCap δ p E q π hπ
          (n - (j : ℕ)) (j.rev : ℕ) α) := sorry

/-- The positive Chern map sums the Chern-relation terms indexed by positive Chern-class
degree. -/
noncomputable def positiveChernMap
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (n : ℤ) :
    ((j : Fin r) →
      @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance (n - (j.succ : ℕ))) →+
      totalSpaceChowGroup δ p E r π hπ (n - 1) :=
  ∑ j : Fin r, (chernTerm δ p E r π hπ n j.succ).comp
    (Pi.evalAddMonoidHom
      (fun i : Fin r ↦ @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance (n - (i.succ : ℕ))) j)

/-- The positive Chern map evaluates as the finite sum of its geometric terms. -/
theorem positiveChernMap_apply
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (n : ℤ)
    (α : (j : Fin r) →
      @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance (n - (j.succ : ℕ))) :
    positiveChernMap δ p E r π hπ n α =
      ∑ j : Fin r, chernTerm δ p E r π hπ n j.succ (α j) := sorry

/-- The positive Chern map of a represented finite-rank projective bundle is bijective. -/
theorem positiveChernMap_bijective
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (n : ℤ) :
    Function.Bijective (positiveChernMap δ p E r π hπ n) := sorry

end AlgebraicGeometry.ChowGroup.ProjectiveBundle.Formula
