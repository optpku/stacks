module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import stacks_project.Chap82.Definition_82_17_1_Cycle

/-!
# Codimension-one Chow groups of good integral algebraic spaces

On an integral good algebraic space, `CH_{n-1}(X)` is the quotient of the group
of `(n-1)`-cycles by the principal cycles of rational units. The first Chern
class of an invertible module capped with `[X]` is the common class of
`div_L(s)` in this group.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open Function

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable [IsIntegral X]

/-- The group `Z_{n-1}(X)` of `(n-1)`-cycles on a good integral algebraic space,
where `n = dim_δ(X)`. -/
noncomputable abbrev codimOneCycleGroup :
    AddSubgroup (Function.locallyFinsupp (Points X) ℤ) :=
  (cycleGroup f) δ ((deltaDimension f) δ (univIrreducibleClosed X) - 1)

/-- Membership in `Z_{n-1}(X)` is membership in the cycle group of degree
`dim_δ(X) - 1`. -/
theorem mem_codimOneCycleGroup (α : Function.locallyFinsupp (Points X) ℤ) :
    α ∈ (codimOneCycleGroup f) δ ↔
      α ∈ (cycleGroup f) δ ((deltaDimension f) δ (univIrreducibleClosed X) - 1) :=
  sorry

/-- An `(n-1)`-cycle is principal when it is the cycle of the principal Weil
divisor of a rational unit. -/
def IsPrincipalCodimOneCycle (α : Function.locallyFinsupp (Points X) ℤ) : Prop :=
  let _ := δ
  ∃ φ : (RationalFunction X)ˣ,
    α =
      WeilDivisor.toCycle
        (@WeilDivisor.ofRationalUnit S X (LocallyOfFiniteType.isLocallyNoetherian f)
          inferInstance φ)

/-- Principality of an `(n-1)`-cycle is equivalent to matching the cycle of some
principal Weil divisor. -/
theorem IsPrincipalCodimOneCycle_iff (α : Function.locallyFinsupp (Points X) ℤ) :
    IsPrincipalCodimOneCycle f δ α ↔
      ∃ φ : (RationalFunction X)ˣ,
        α =
          WeilDivisor.toCycle
            (@WeilDivisor.ofRationalUnit S X
              (LocallyOfFiniteType.isLocallyNoetherian f) inferInstance φ) :=
  sorry

/-- The subgroup of principal `(n-1)`-cycles on a good integral algebraic space. -/
noncomputable def principalCycles : AddSubgroup ((codimOneCycleGroup f) δ) where
  carrier := {α | IsPrincipalCodimOneCycle f δ (α : Function.locallyFinsupp (Points X) ℤ)}
  zero_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry

/-- Membership in the principal `(n-1)`-cycle subgroup is the principal-cycle
predicate. -/
theorem mem_principalCycles_iff (α : (codimOneCycleGroup f) δ) :
    α ∈ (principalCycles f) δ ↔
      IsPrincipalCodimOneCycle f δ (α : Function.locallyFinsupp (Points X) ℤ) :=
  sorry

/-- The codimension-one Chow group `CH_{n-1}(X)` of a good integral algebraic
space. -/
noncomputable abbrev codimOneChowGroup :=
  (codimOneCycleGroup f) δ ⧸ (principalCycles f) δ

/-- The class of an `(n-1)`-cycle in `CH_{n-1}(X)`. Cycles outside
`Z_{n-1}(X)` are sent to `0`. -/
noncomputable def chowClass (α : Function.locallyFinsupp (Points X) ℤ) :
    (codimOneChowGroup f) δ :=
  @dite ((codimOneChowGroup f) δ) (α ∈ (codimOneCycleGroup f) δ)
    (Classical.propDecidable _)
    (fun h ↦ QuotientAddGroup.mk' ((principalCycles f) δ) ⟨α, h⟩)
    (fun _ ↦ 0)

/-- On `(n-1)`-cycles, `chowClass` is the canonical quotient map. -/
theorem chowClass_eq_mk (α : Function.locallyFinsupp (Points X) ℤ)
    (hα : α ∈ (codimOneCycleGroup f) δ) :
    (chowClass f) δ α = QuotientAddGroup.mk' ((principalCycles f) δ) ⟨α, hα⟩ :=
  sorry

/-- Two `(n-1)`-cycles determine the same class in `CH_{n-1}(X)` if and only if
their difference is principal. -/
theorem chowClass_eq_iff (α β : Function.locallyFinsupp (Points X) ℤ)
    (hα : α ∈ (codimOneCycleGroup f) δ) (hβ : β ∈ (codimOneCycleGroup f) δ) :
    (chowClass f) δ α = (chowClass f) δ β ↔
      IsPrincipalCodimOneCycle f δ (α - β) :=
  sorry

/-- The class `c1(L) ∩ [X]` in `CH_{n-1}(X)`, selected as the common Chow class
of `div_L(s)` for every nonzero meromorphic section of `L`. -/
noncomputable def firstChernCapFundamental (L : X.Modules) [isInvertibleObject L] :
    (codimOneChowGroup f) δ :=
  @Classical.epsilon ((codimOneChowGroup f) δ) ⟨(0 : (codimOneChowGroup f) δ)⟩
    fun c ↦
      ∀ (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s),
        c = (chowClass f) δ ((meromorphicSectionDivisorCycle f) δ s hs)

/-- The class `c1(L) ∩ [X]` equals the Chow class of `div_L(s)` for any nonzero
meromorphic section of `L`. -/
theorem firstChernCapFundamental_eq (L : X.Modules) [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s) :
    firstChernCapFundamental f δ L =
      (chowClass f) δ ((meromorphicSectionDivisorCycle f) δ s hs) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
