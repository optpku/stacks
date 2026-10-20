/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszlo.GlueableFunctor

/-!
# Lemma 81.12.4

For a Beauville–Laszlo glueing pair, the canonical functor
`Over (space R) ⥤ category R' f` is faithful on the full subcategory of
glueable algebraic spaces over `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing

noncomputable section

universe u

/- Lemma 81.12.4: let `(algebraMap R R', f)` be a glueing pair. The canonical
functor on glueable algebraic spaces over `Spec R` is faithful. -/
@[stacks 0F9S] #check
  (AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing.glueableFunctor_faithful :
    {R R' : Type u} → [CommRing R] → [CommRing R'] → [Algebra R R'] → (f : R) →
      [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f] →
      (glueableFunctor R' f).Faithful)

#check
  (AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing.functor_map_injective :
    {R R' : Type u} → [CommRing R] → [CommRing R'] → [Algebra R R'] → (f : R) →
      [IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f] →
      {Y Z : Over (space R)} → (hY : glueableProperty R' f Y) →
        (hZ : glueableProperty R' f Z) →
        Function.Injective (fun α : Y ⟶ Z ↦ (functor R' f).map α))
