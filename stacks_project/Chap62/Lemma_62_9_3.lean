module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Cover.H
public import stacks_project.Chap62.Lemma_62_6_6_Relative
public import stacks_project.Chap62.Lemma_62_7_3_Operations
public import stacks_project.Chap62.Lemma_62_9_2_Proper

/-!
# Descent of properness of relative cycles along h coverings

A relative `r`-cycle on `X / S` is proper if and only if every base change
along an h covering of `S` is proper.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Hom
open CyclesOnFibers

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- Lemma 62.9.3: if `f : X ⟶ S` is locally of finite type, `S` is locally
Noetherian, `α` is a relative `r`-cycle on `X / S`, and `family` is an h
covering of `S`, then `α` is proper if and only if each base change of `α`
along `(family i).hom` is proper. -/
@[stacks 0H63]
theorem proper_iff_hCovering_baseChange {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ)
    (α : CyclesOnFibers f r) (hα : RelativeCycle.IsRelative α)
    {ι : Type v} (family : ι → Over S) [Scheme.HCovering family] :
    Proper α ↔ ∀ i, Proper (baseChange α (family i).hom) := sorry

/-- If every base change of a relative `r`-cycle along an h covering is proper,
then the relative cycle is proper. -/
theorem proper_of_hCovering_baseChange {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ)
    (α : CyclesOnFibers f r) (hα : RelativeCycle.IsRelative α)
    {ι : Type v} (family : ι → Over S) [Scheme.HCovering family]
    (h : ∀ i, Proper (baseChange α (family i).hom)) :
    Proper α := sorry

end AlgebraicGeometry
