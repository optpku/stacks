module

public import stacks_project.Chap101.Lemma_101_16_1

/-!
# Smooth-local-on-source-and-target morphisms of algebraic stacks

A morphism property of algebraic spaces that is smooth local on the
source-and-target lifts to morphisms of algebraic stacks by testing it on a
smooth algebraic-space presentation square with surjective source atlas.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism `f : X ⟶ Y` of algebraic stacks has a morphism property `P` of
algebraic spaces that is smooth local on the source-and-target when some smooth
algebraic-space presentation square with surjective source atlas has `P` on the
top arrow. -/
def hasSmoothLocalAtSourceAndTarget {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P] {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  existsSurjectiveSmoothSquare P f

/-- `hasSmoothLocalAtSourceAndTarget P f` is the existence of a smooth
surjective algebraic-space presentation whose top arrow has `P`. -/
theorem hasSmoothLocalAtSourceAndTarget_def {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P] {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    hasSmoothLocalAtSourceAndTarget P f ↔ existsSurjectiveSmoothSquare P f :=
  sorry

namespace hasSmoothLocalAtSourceAndTarget

/-- A smooth surjective algebraic-space presentation whose top arrow has `P`
witnesses `hasSmoothLocalAtSourceAndTarget P f`. -/
theorem of {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P] {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y} {U V : AlgebraicSpace S}
    {a : U.toGroupoids ⟶ X} {b : V.toGroupoids ⟶ Y} {h : U ⟶ V}
    (hpres : IsSmoothSurjectivePresentation f a b h) (hP : P h) :
    hasSmoothLocalAtSourceAndTarget P f :=
  sorry

/-- A morphism satisfying `hasSmoothLocalAtSourceAndTarget P f` admits a smooth
surjective algebraic-space presentation whose top arrow has `P`. -/
theorem spec {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P] {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : hasSmoothLocalAtSourceAndTarget P f) :
    ∃ (U V : AlgebraicSpace S) (a : U.toGroupoids ⟶ X) (b : V.toGroupoids ⟶ Y)
      (h : U ⟶ V), IsSmoothSurjectivePresentation f a b h ∧ P h :=
  sorry

end hasSmoothLocalAtSourceAndTarget

/-- A morphism of algebraic stacks has the smooth-local-on-source-and-target
lift of `P` if and only if every smooth algebraic-space presentation square
with smooth comparison has `P` on the top arrow. -/
theorem hasSmoothLocalAtSourceAndTarget_iff_forallSmoothComparison
    {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P] {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    hasSmoothLocalAtSourceAndTarget P f ↔ forallSmoothComparison P f :=
  sorry

/-- If `X` and `Y` are algebraic spaces, then `hasSmoothLocalAtSourceAndTarget P`
on the associated 1-morphism is equivalent to `P` on the evaluated morphism of
algebraic spaces. -/
theorem hasSmoothLocalAtSourceAndTarget_iff_eval {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P] {U V : AlgebraicSpace S}
    (f : U.toGroupoids ⟶ V.toGroupoids) :
    hasSmoothLocalAtSourceAndTarget P f ↔
      P (AlgebraicSpace.toGroupoids.eval f) :=
  sorry

/-- If `P` is also stable under base change and fppf local on the target, then
for a morphism representable by algebraic spaces the
smooth-local-on-source-and-target lift of `P` is equivalent to
`Groupoids.Hom.has P`. -/
theorem hasSmoothLocalAtSourceAndTarget_iff_has {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f) :
    hasSmoothLocalAtSourceAndTarget P f ↔ Groupoids.Hom.has P f :=
  sorry

/-- Transport of `hasSmoothLocalAtSourceAndTarget P` along presentations of
algebraic stacks by algebraic spaces recovers `P` on the induced morphism of
algebraic spaces. -/
theorem hasSmoothLocalAtSourceAndTarget_iff_recover {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    {U V : AlgebraicSpace S} (eX : X ≌ U.toGroupoids)
    (eY : Y ≌ V.toGroupoids) (f : X ⟶ Y) :
    hasSmoothLocalAtSourceAndTarget P f ↔
      P (AlgebraicSpace.toGroupoids.recover eX eY f) :=
  sorry

/-- A morphism of algebraic spaces that has `P` induces a 1-morphism of
algebraic stacks that has the smooth-local-on-source-and-target lift of `P`. -/
theorem hasSmoothLocalAtSourceAndTarget_map {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P] {U V : AlgebraicSpace S}
    {h : U ⟶ V} (hh : P h) :
    hasSmoothLocalAtSourceAndTarget P (AlgebraicSpace.toGroupoids.map h) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
