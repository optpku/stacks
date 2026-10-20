module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Effective
public import ReasLib.AlgebraicGeometry.RelativeCycle
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.Operations

/-!
# Effective families of cycles on fibres

Effectiveness of an integer-degree family of fibre cycles is equivalent to
nonnegativity of all its fibre coefficients.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.CyclesOnFibers

/-- A family of `r`-cycles on the fibres of `f` is effective if every fibre
cycle is an effective algebraic cycle. -/
def IsEffective {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℤ}
    (α : CyclesOnFibers f r) : Prop :=
  ∀ s : S, α.toAlgebraicCycle s ∈ AlgebraicCycle.effective (f.fiber s)

/-- Effectiveness of a fibrewise family is equivalent to nonnegativity of every
fibre coefficient. -/
theorem isEffective_iff {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℤ}
    (α : CyclesOnFibers f r) :
    IsEffective α ↔
      ∀ s : S, ∀ x : f.fiber s, 0 ≤ α.toAlgebraicCycle s x := sorry

/-- Effectiveness of a family of fibre cycles is preserved by flat pullback along a
morphism of relative dimension `e`. -/
theorem IsEffective.flatPullback {X' X S : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {r : ℕ} {α : CyclesOnFibers f r} (hα : α.IsEffective)
    (h : X' ⟶ X) (e : ℕ) [Flat h] [RelativeDimension h e] :
    IsEffective (Scheme.Hom.FiberCycleFamily.flatPullback h rfl e α) := sorry

/-- A relative cycle over a locally Noetherian base is effective if and only if
its flat pullbacks along a jointly surjective family of morphisms of common
relative dimension are effective. -/
theorem isEffective_iff_forall_flatPullback {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r e : ℕ) {ι : Type u}
    (family : ι → Over X) [∀ i, Flat (family i).hom]
    [∀ i, RelativeDimension (family i).hom e]
    (h_surj : Function.Surjective fun p : Σ i, (family i).left ↦ (family p.1).hom p.2)
    (α : CyclesOnFibers f r) (hα : RelativeCycle.IsRelative α) :
    α.IsEffective ↔
      ∀ i, IsEffective (Scheme.Hom.FiberCycleFamily.flatPullback (family i).hom rfl e α) :=
  sorry

/-- If every flat pullback of a relative cycle along a jointly surjective family
of morphisms of common relative dimension is effective, then the relative cycle
is effective. -/
theorem isEffective_of_forall_flatPullback {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r e : ℕ) {ι : Type u}
    (family : ι → Over X) [∀ i, Flat (family i).hom]
    [∀ i, RelativeDimension (family i).hom e]
    (h_surj : Function.Surjective fun p : Σ i, (family i).left ↦ (family p.1).hom p.2)
    (α : CyclesOnFibers f r) (hα : RelativeCycle.IsRelative α)
    (h_eff : ∀ i,
      IsEffective (Scheme.Hom.FiberCycleFamily.flatPullback (family i).hom rfl e α)) :
    α.IsEffective :=
  (isEffective_iff_forall_flatPullback f r e family h_surj α hα).mpr h_eff

end AlgebraicGeometry.Scheme.Hom.CyclesOnFibers
