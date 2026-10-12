/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Over
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Remark_67_22_3_EtaleLocal

/-!
# Étale-local properties of morphisms of algebraic spaces

A scheme-morphism property that is étale local on source-and-target may be
tested on a single surjective étale scheme square. On representable spaces this
recovers the underlying scheme morphism, and on representable morphisms it
recovers the Section 67.3 / Definition 65.5.1 predicate when `P` is stable under
base change and fppf local on the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- There is a commutative square with étale vertical arrows from schemes,
surjective source atlas, and top arrow satisfying `P`. -/
def etaleLocal.existsSurjectiveSquare {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) [IsEtaleLocalAtSourceAndTarget P]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  ∃ (U V : Over S) (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
    (over (@AlgebraicGeometry.Etale)).presheaf a ∧
      (over (@AlgebraicGeometry.Etale)).presheaf b ∧
        a ≫ f = yoneda.map h ≫ b ∧
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) a ∧
            P h.left

/-- Lemma 67.22.1 (1): a morphism of algebraic spaces over `S` has the étale-local
lift of `P` if and only if some commutative square with étale vertical arrows
from schemes and surjective source atlas has top arrow satisfying `P`. -/
@[stacks 03MJ]
theorem etaleLocal_iff_existsSurjectiveSquare {S : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}} [IsEtaleLocalAtSourceAndTarget P]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    etaleLocal P f ↔ etaleLocal.existsSurjectiveSquare P f :=
  sorry

/-- Lemma 67.22.1 (2): if `X` and `Y` are representable, then the étale-local lift
of `P` on the induced morphism of algebraic spaces is equivalent to the
underlying scheme morphism having `P`. -/
@[stacks 03MJ]
theorem etaleLocal_ofOverMap_iff {S : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}} [IsEtaleLocalAtSourceAndTarget P]
    {U V : Over S} (h : U ⟶ V) :
    etaleLocal P (ofOverMap h) ↔ P h.left :=
  sorry

/-- Lemma 67.22.1 (3): if `P` is stable under arbitrary base change and fppf local
on the target, then a representable morphism of algebraic spaces has the
étale-local lift of `P` if and only if it has `P` in the sense of Section 67.3. -/
@[stacks 03MJ]
theorem etaleLocal_iff_over_presheaf {S : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}} [IsEtaleLocalAtSourceAndTarget P]
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    etaleLocal P f ↔ (over P).presheaf f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
