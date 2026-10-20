/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Equivalence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.IsoComma.LocallySurjective
import StacksCheckRecall

/-!
# Equivalence of induced morphisms of quotient stacks

This file records the criterion that `[f] : [U/R] ⟶ [U'/R']` is an equivalence
if and only if the source groupoid is the restriction of the target along the
object map and the structure map `h : U ×_{f, U', t'} R' ⟶ U'` is a surjection
of fppf sheaves, together with the standard sufficient conditions for the
latter.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 78.25.2. Notation and assumption as in Lemma 78.21.1. The morphism of
quotient stacks `[f] : [U/R] ⟶ [U'/R']` is an equivalence if and only if
`(U, R, s, t, c)` is the restriction of `(U', R', s', t', c')` via
`f.obj : U ⟶ U'`, and `h = isoCommaToTargetObject f : U ×_{f, U', t'} R' ⟶ U'`
is a surjection of fppf sheaves. -/
@[stacks 046T] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.quotientStackMap_isEquivalence_iff :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
      {G H : GroupoidAlgebraicSpace B} (f : GroupoidAlgebraicSpace.Hom G H),
      f.quotientStackMap.toBasedFunctor.IsEquivalence ↔
        GroupoidAlgebraicSpace.Hom.IsRestriction f ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
            (GroupoidAlgebraicSpace.Hom.isoCommaToTargetObject f).left)

/- If `{h : U ×_{f, U', t'} R' ⟶ U'}` is an fppf covering, then
`isoCommaToTargetObject f` is a surjection of fppf sheaves. -/
#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.isoCommaToTargetObject_isLocallySurjective_of_fppfCovering :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
      (f : GroupoidAlgebraicSpace.Hom G H)
      [FppfCovering (fun _ : PUnit ↦ (GroupoidAlgebraicSpace.Hom.isoComma f).U.left)
        (fun _ ↦ (GroupoidAlgebraicSpace.Hom.isoCommaToTargetObject f).left)],
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
        (GroupoidAlgebraicSpace.Hom.isoCommaToTargetObject f).left)

/- If `f.obj : U ⟶ U'` is a surjection of fppf sheaves, then
`isoCommaToTargetObject f` is a surjection of fppf sheaves. -/
#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.isoCommaToTargetObject_isLocallySurjective_of_obj :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
      (f : GroupoidAlgebraicSpace.Hom G H)
      (h_obj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) f.obj.left),
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
        (GroupoidAlgebraicSpace.Hom.isoCommaToTargetObject f).left)

/- If `{f.obj : U ⟶ U'}` is an fppf covering, then `isoCommaToTargetObject f`
is a surjection of fppf sheaves. -/
#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.isoCommaToTargetObject_isLocallySurjective_of_obj_fppfCovering :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
      (f : GroupoidAlgebraicSpace.Hom G H)
      [FppfCovering (fun _ : PUnit ↦ G.U.left) (fun _ ↦ f.obj.left)],
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
        (GroupoidAlgebraicSpace.Hom.isoCommaToTargetObject f).left)
