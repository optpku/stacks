module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import stacks_project.Chap73.Definition_73_7_1_FppfCover
public import stacks_project.Chap78.Lemma_78_21_1_QuotientMap
public import stacks_project.Chap78.Lemma_78_21_2_IsoComma
public import stacks_project.Chap78.Lemma_78_25_1_Restriction

/-!
# Equivalence of induced morphisms of quotient stacks

This file records the criterion that `[f] : [U/R] ⟶ [U'/R']` is an equivalence
if and only if the source groupoid is the restriction of the target along the
object map and the structure map `h : U ×_{f, U', t'} R' ⟶ U'` is a surjection
of fppf sheaves, together with the standard sufficient conditions for the
latter.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.Hom

/-- Lemma 78.25.2. Notation and assumption as in Lemma 78.21.1. The morphism of
quotient stacks `[f] : [U/R] ⟶ [U'/R']` is an equivalence if and only if
`(U, R, s, t, c)` is the restriction of `(U', R', s', t', c')` via
`f.obj : U ⟶ U'`, and `h = isoCommaToTargetObject f : U ×_{f, U', t'} R' ⟶ U'`
is a surjection of fppf sheaves. -/
@[stacks 046T]
theorem quotientStackMap_isEquivalence_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) :
    f.quotientStackMap.toBasedFunctor.IsEquivalence ↔
      IsRestriction f ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
          (isoCommaToTargetObject f).left := sorry

/-- If `{h : U ×_{f, U', t'} R' ⟶ U'}` is an fppf covering, then
`isoCommaToTargetObject f` is a surjection of fppf sheaves. -/
instance isoCommaToTargetObject_isLocallySurjective_of_fppfCovering
    {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H)
    [FppfCovering (fun _ : PUnit ↦ (isoComma f).U.left)
      (fun _ ↦ (isoCommaToTargetObject f).left)] :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (isoCommaToTargetObject f).left := sorry

/-- If `f.obj : U ⟶ U'` is a surjection of fppf sheaves, then
`isoCommaToTargetObject f` is a surjection of fppf sheaves. -/
theorem isoCommaToTargetObject_isLocallySurjective_of_obj {S : Scheme.{u}}
    {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B} (f : Hom G H)
    (h_obj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) f.obj.left) :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (isoCommaToTargetObject f).left := sorry

/-- If `{f.obj : U ⟶ U'}` is an fppf covering, then `isoCommaToTargetObject f`
is a surjection of fppf sheaves. -/
instance isoCommaToTargetObject_isLocallySurjective_of_obj_fppfCovering
    {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H)
    [FppfCovering (fun _ : PUnit ↦ G.U.left) (fun _ ↦ f.obj.left)] :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (isoCommaToTargetObject f).left := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.Hom
