/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap73.Lemma_73_7_3_Precoverage
public import stacks_project.Chap74.Definition_74_21_1_EtaleSmoothLocal
public import stacks_project.Chap94.«94_8_2_1_FullyFaithful»
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty
public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Definition_101_34_2_Presentation

/-!
# Étale-smooth-local-on-source-and-target morphisms of algebraic stacks

A morphism property of algebraic spaces that is étale-smooth local on the
source-and-target lifts to morphisms of algebraic stacks by testing it on a
mixed étale-smooth algebraic-space presentation square with surjective source
atlas. For a DM morphism this is equivalent to the same condition on every
such square.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism `f : X ⟶ Y` of algebraic stacks has a morphism property `P` of
algebraic spaces that is étale-smooth local on the source-and-target when some
mixed étale-smooth algebraic-space presentation square with étale comparison
and surjective source atlas has `P` on the top arrow. For a DM morphism this
is equivalent to the same condition on every such square. -/
def hasEtaleSmoothLocalAtSourceAndTarget {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    [AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P] {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  existsSurjectiveEtaleSmoothSquare P f

/-- `hasEtaleSmoothLocalAtSourceAndTarget P f` is the existence of an
étale-smooth surjective algebraic-space presentation whose top arrow has `P`. -/
theorem hasEtaleSmoothLocalAtSourceAndTarget_def {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    [AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P] {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    hasEtaleSmoothLocalAtSourceAndTarget P f ↔
      existsSurjectiveEtaleSmoothSquare P f :=
  sorry

namespace hasEtaleSmoothLocalAtSourceAndTarget

/-- An étale-smooth surjective algebraic-space presentation whose top arrow has
`P` witnesses `hasEtaleSmoothLocalAtSourceAndTarget P f`. -/
theorem of {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P] {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} {U V : AlgebraicSpace S}
    {a : U.toGroupoids ⟶ X} {b : V.toGroupoids ⟶ Y} {h : U ⟶ V}
    (hpres : IsEtaleSmoothSurjectivePresentation f a b h) (hP : P h) :
    hasEtaleSmoothLocalAtSourceAndTarget P f :=
  sorry

/-- A morphism satisfying `hasEtaleSmoothLocalAtSourceAndTarget P f` admits an
étale-smooth surjective algebraic-space presentation whose top arrow has `P`. -/
theorem spec {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P] {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : hasEtaleSmoothLocalAtSourceAndTarget P f) :
    ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
      (h : U ⟶ V), IsEtaleSmoothSurjectivePresentation f a b h ∧ P h :=
  sorry

end hasEtaleSmoothLocalAtSourceAndTarget

/-- A DM morphism of algebraic stacks has the étale-smooth-local-on-source-and-target
lift of `P` if and only if every étale-smooth algebraic-space presentation
square with étale comparison has `P` on the top arrow. -/
theorem hasEtaleSmoothLocalAtSourceAndTarget_iff_forallEtaleSmoothComparison
    {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    [AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P] {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [DM f] :
    hasEtaleSmoothLocalAtSourceAndTarget P f ↔ forallEtaleSmoothComparison P f :=
  sorry

/-- If `X` and `Y` are algebraic spaces, then `hasEtaleSmoothLocalAtSourceAndTarget P`
on the associated 1-morphism is equivalent to `P` on the evaluated morphism of
algebraic spaces. -/
theorem hasEtaleSmoothLocalAtSourceAndTarget_iff_eval {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    [AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P] {U V : AlgebraicSpace S}
    (f : U.toGroupoids ⟶ V.toGroupoids) :
    hasEtaleSmoothLocalAtSourceAndTarget P f ↔
      P (AlgebraicSpace.toGroupoids.eval f) :=
  sorry

/-- If `P` is also stable under base change and fppf local on the target, then
for a morphism representable by algebraic spaces the
étale-smooth-local-on-source-and-target lift of `P` is equivalent to
`Groupoids.Hom.has P`. -/
theorem hasEtaleSmoothLocalAtSourceAndTarget_iff_has {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P]
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f) :
    hasEtaleSmoothLocalAtSourceAndTarget P f ↔ Groupoids.Hom.has P f :=
  sorry

/-- Transport of `hasEtaleSmoothLocalAtSourceAndTarget P` along presentations of
algebraic stacks by algebraic spaces recovers `P` on the induced morphism of
algebraic spaces. -/
theorem hasEtaleSmoothLocalAtSourceAndTarget_iff_recover {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P]
    {U V : AlgebraicSpace S} (eX : X ≌ U.toGroupoids)
    (eY : Y ≌ V.toGroupoids) (f : X ⟶ Y) :
    hasEtaleSmoothLocalAtSourceAndTarget P f ↔
      P (AlgebraicSpace.toGroupoids.recover eX eY f) :=
  sorry

/-- A morphism of algebraic spaces that has `P` induces a 1-morphism of
algebraic stacks that has the étale-smooth-local-on-source-and-target lift of
`P`. -/
theorem hasEtaleSmoothLocalAtSourceAndTarget_map {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    [AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P] {U V : AlgebraicSpace S}
    {h : U ⟶ V} (hh : P h) :
    hasEtaleSmoothLocalAtSourceAndTarget P (AlgebraicSpace.toGroupoids.map h) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
