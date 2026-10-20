/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RepresentableProperty.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

/- Lemma 65.5.6: let `S` be a scheme and let `F`, `G`, `H` be presheaves of sets
`(Over S)ᵒᵖ ⥤ Type u` on `(Sch/S)_fppf`. Let `P` be a property of morphisms of
schemes in the sense of Definition 65.5.1. Let `a : F ⟶ G` be a representable
transformation of functors, and let `b : H ⟶ G` be any transformation. In the
fibre product square, write `a' = pullback.fst b a`. If `b` is locally
surjective for `Scheme.fppfTopology.over S` (equivalently, the sheafified map
`H# ⟶ G#` is an epimorphism of fppf sheaves), and if `a'` has property `P` in
the sense of `(over P).presheaf`, then `a` has property `P`. -/
@[stacks 03KD] #check
  (AlgebraicGeometry.Scheme.representableMorphismProperty.of_pullback_fst :
    ∀ {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u}
      (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
      [P.IsLocalAtTarget Scheme.fppfPrecoverage] {a : F ⟶ G} {b : H ⟶ G}
      [HasPullback b a] (ha : yoneda.relativelyRepresentable a)
      (h_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) b)
      (ha' : AlgebraicGeometry.Scheme.representableMorphismProperty S P
        (pullback.fst b a)),
      AlgebraicGeometry.Scheme.representableMorphismProperty S P a)

#check
  (AlgebraicGeometry.Scheme.representableMorphismProperty.pullback_fst_iff :
    ∀ {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u}
      (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
      [P.IsLocalAtTarget Scheme.fppfPrecoverage] {a : F ⟶ G} {b : H ⟶ G}
      [HasPullback b a] (ha : yoneda.relativelyRepresentable a)
      (h_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) b),
      AlgebraicGeometry.Scheme.representableMorphismProperty S P
          (pullback.fst b a) ↔
        AlgebraicGeometry.Scheme.representableMorphismProperty S P a)
