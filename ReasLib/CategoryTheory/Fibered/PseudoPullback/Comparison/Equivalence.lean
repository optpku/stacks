/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
-- `FiberedCategory.Fibered` is public because this leaf owns exactly the choice-dependent
-- comparison equivalences obtained from fibredness of one cospan source.
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import ReasLib.CategoryTheory.Functor.Equivalence
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Comparison.Functor

/-!
# Fibred comparison equivalences for explicit pseudo-pullbacks

The deterministic comparison functor is owned by `PseudoPullback.Comparison.Functor`. This leaf
adds the proposition-level equivalence criterion and packages its two symmetric choices as
category equivalences, together with the base-projection compatibility required by applications
over `C`.
-/

@[expose] public section

universe v u vX uX vY uY vZ uZ

namespace CategoryTheory

open BasedCategory
open CategoryTheory.Limits
open CategoricalPullback
open Functor
open scoped CategoricalPullback

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {Z : BasedCategory.{vZ, uZ} C}

namespace BasedCategory.PseudoPullback.Comparison

/-- The canonical comparison functor is an equivalence when the right source projection is
fibred.

Proof strategy: faithfulness follows from extensionality of explicit two-fibre-product morphisms.
For fullness, the pullback compatibility forces the two components to have the same base map.
For essential surjectivity, cartesian-lift the right component along the base isomorphism of an
ordinary pullback object and factor its comparison through that lift; this produces an isomorphic
object whose two components lie over one base object. -/
instance functor.isEquivalence
    [Y.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (functor F G).IsEquivalence := sorry

/-- The canonical comparison functor is also an equivalence when the left source projection is
fibred. This symmetric proposition-level entry point is not registered as an instance, avoiding
overlapping typeclass paths when both sources are fibred. -/
theorem functor.isEquivalenceOfLeft
    [X.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (functor F G).IsEquivalence := sorry

/-- When the right source is fibred, the explicit same-fiber pseudo-pullback is canonically
equivalent, as a category, to the ordinary categorical pullback of the underlying functors. -/
@[stacks 0H2E]
noncomputable def equivalence
    [Y.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (PseudoPullback F G).obj ≌ F.toFunctor ⊡ G.toFunctor :=
  (functor F G).asEquivalence

/-- The forward functor of the selected right-fibred comparison equivalence is the deterministic
comparison functor. -/
@[simp]
theorem equivalence.functor
    [Y.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (equivalence F G).functor = functor F G := sorry

/-- The forward functor of the right-fibred comparison equivalence is compatible with the first
base projection. This is the universe-polymorphic transport of `fstBaseIso` across
`equivalence.functor`. -/
noncomputable def equivalence.functor.fstBaseIso
    [Y.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (equivalence F G).functor ⋙
        (π₁ F.toFunctor G.toFunctor ⋙ X.p) ≅
      (PseudoPullback F G).p :=
  Functor.isoWhiskerRight (eqToIso (equivalence.functor F G))
      (π₁ F.toFunctor G.toFunctor ⋙ X.p) ≪≫
    CategoryTheory.BasedCategory.PseudoPullback.Comparison.fstBaseIso F G

/-- The forward functor of the right-fibred comparison equivalence is compatible with the second
base projection. This is the universe-polymorphic transport of `sndBaseIso` across
`equivalence.functor`. -/
noncomputable def equivalence.functor.sndBaseIso
    [Y.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (equivalence F G).functor ⋙
        (π₂ F.toFunctor G.toFunctor ⋙ Y.p) ≅
      (PseudoPullback F G).p :=
  Functor.isoWhiskerRight (eqToIso (equivalence.functor F G))
      (π₂ F.toFunctor G.toFunctor ⋙ Y.p) ≪≫
    CategoryTheory.BasedCategory.PseudoPullback.Comparison.sndBaseIso F G

/-- When the left source is fibred, select the same canonical comparison equivalence without
requiring callers to install a temporary overlapping `IsEquivalence` instance. -/
@[stacks 0H2E "left-fibred pseudo-pullback comparison equivalence"]
noncomputable def equivalenceOfLeft
    [X.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (PseudoPullback F G).obj ≌ F.toFunctor ⊡ G.toFunctor :=
  (functor F G).asEquivalenceOf (functor.isEquivalenceOfLeft F G)

/-- The forward functor of the selected left-fibred comparison equivalence is the deterministic
comparison functor. -/
@[simp]
theorem equivalenceOfLeft.functor
    [X.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (equivalenceOfLeft F G).functor = functor F G := sorry

/-- The forward functor of the left-fibred comparison equivalence is compatible with the first
base projection. -/
noncomputable def equivalenceOfLeft.functor.fstBaseIso
    [X.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (equivalenceOfLeft F G).functor ⋙
        (π₁ F.toFunctor G.toFunctor ⋙ X.p) ≅
      (PseudoPullback F G).p :=
  Functor.isoWhiskerRight (eqToIso (equivalenceOfLeft.functor F G))
      (π₁ F.toFunctor G.toFunctor ⋙ X.p) ≪≫
    CategoryTheory.BasedCategory.PseudoPullback.Comparison.fstBaseIso F G

/-- The forward functor of the left-fibred comparison equivalence is compatible with the second
base projection. -/
noncomputable def equivalenceOfLeft.functor.sndBaseIso
    [X.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (equivalenceOfLeft F G).functor ⋙
        (π₂ F.toFunctor G.toFunctor ⋙ Y.p) ≅
      (PseudoPullback F G).p :=
  Functor.isoWhiskerRight (eqToIso (equivalenceOfLeft.functor F G))
      (π₂ F.toFunctor G.toFunctor ⋙ Y.p) ≪≫
    CategoryTheory.BasedCategory.PseudoPullback.Comparison.sndBaseIso F G

/-- Inverse form of the left projection compatibility for the right-fibred selected equivalence. -/
noncomputable def equivalence.inverse.fstBaseIso
    [Y.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (equivalence F G).inverse ⋙
        (PseudoPullback F G).p ≅
      π₁ F.toFunctor G.toFunctor ⋙ X.p :=
  Iso.inverseCompIso
    (equivalence.functor.fstBaseIso F G).symm

/-- Inverse form of the right projection compatibility for the right-fibred selected
equivalence. -/
noncomputable def equivalence.inverse.sndBaseIso
    [Y.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (equivalence F G).inverse ⋙
        (PseudoPullback F G).p ≅
      π₂ F.toFunctor G.toFunctor ⋙ Y.p :=
  Iso.inverseCompIso
    (equivalence.functor.sndBaseIso F G).symm

/-- Inverse form of the left projection compatibility for the left-fibred selected
equivalence. -/
noncomputable def equivalenceOfLeft.inverse.fstBaseIso
    [X.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (equivalenceOfLeft F G).inverse ⋙
        (PseudoPullback F G).p ≅
      π₁ F.toFunctor G.toFunctor ⋙ X.p :=
  Iso.inverseCompIso
    (equivalenceOfLeft.functor.fstBaseIso F G).symm

/-- Inverse form of the right projection compatibility for the left-fibred selected
equivalence. -/
noncomputable def equivalenceOfLeft.inverse.sndBaseIso
    [X.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (equivalenceOfLeft F G).inverse ⋙
        (PseudoPullback F G).p ≅
      π₂ F.toFunctor G.toFunctor ⋙ Y.p :=
  Iso.inverseCompIso
    (equivalenceOfLeft.functor.sndBaseIso F G).symm

end BasedCategory.PseudoPullback.Comparison

end CategoryTheory
