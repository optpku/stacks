/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_30_4_Pullback
public import stacks_project.Chap67.Lemma_67_40_3_Pullback
public import stacks_project.Chap76.«76_42_5_1_ProperSupport»
public import stacks_project.Chap99.Lemma_99_10_1_Picard

/-!
# Natural inclusion of the Picard category into the coherent category

The identity-on-triples functor sends an invertible module on a fibre to the
same triple, now viewed as a finitely presented module that is flat over the
test scheme with proper support.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- An invertible module on an algebraic space is of finite presentation. -/
instance instIsFinitePresentation_of_isInvertible {Y : AlgebraicSpace S}
    (L : Y.Modules) [isInvertibleObject L] : L.IsFinitePresentation := sorry

/-- Finite presentation of an invertible module, with invertibility passed
explicitly. -/
theorem isFinitePresentation_of_isInvertible {Y : AlgebraicSpace S}
    (L : Y.Modules) (h : isInvertibleObject L) : L.IsFinitePresentation := sorry

/-- The projection `X_T ⟶ T` of a fibre of a flat morphism is flat. -/
instance fiberToBase_flat (f : X ⟶ B) [Flat f] (σ : CohStack.SchemesOver B) :
    Flat (CohStack.fiberToBase f σ) :=
  flat_pullback_snd f σ.hom

/-- The projection `X_T ⟶ T` of a fibre of a proper morphism is proper. -/
instance fiberToBase_proper (f : X ⟶ B) [Proper f] (σ : CohStack.SchemesOver B) :
    Proper (CohStack.fiberToBase f σ) :=
  proper_pullback_snd f σ.hom

/-- An invertible module on a fibre is flat over the test scheme whenever the
fibre projection is flat. -/
theorem flatOver_of_isInvertible {Y Z : AlgebraicSpace S} (L : Y.Modules)
    (g : Y ⟶ Z) (hL : isInvertibleObject L) (hg : Flat g) :
    CohStack.flatOver L g := sorry

/-- The identity-on-triples functor sending a Picard object `(T, g, L)` to the
same triple, viewed as an object of `CohStack.Obj f`. -/
def toCoh (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f] :
    Obj f ⥤ CohStack.Obj f where
  obj x :=
    { σ := x.σ
      module := x.line
      isFinitePresentation := isFinitePresentation_of_isInvertible x.line x.invertible
      isFlat :=
        flatOver_of_isInvertible x.line (CohStack.fiberToBase f x.σ) x.invertible
          (fiberToBase_flat f x.σ)
      hasProperSupport :=
        Modules.instHasProperSupportOver_of_proper (CohStack.fiberToBase f x.σ) x.line }
  map α := CohStack.homMk α.base α.iso
  map_id := sorry
  map_comp := sorry

/-- `toCoh` preserves the underlying test scheme. -/
theorem toCoh_obj_σ (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f]
    (x : Obj f) : ((toCoh f).obj x).σ = x.σ := sorry

/-- `toCoh` preserves the underlying module on the fibre. -/
theorem toCoh_obj_module (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f]
    (x : Obj f) : ((toCoh f).obj x).module = x.line := sorry

/-- The identity-on-triples functor lies strictly over `Over S`. -/
theorem toCoh_p (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f] :
    toCoh f ⋙ CohStack.p f = p f := sorry

end AlgebraicGeometry.AlgebraicSpace.Picard
