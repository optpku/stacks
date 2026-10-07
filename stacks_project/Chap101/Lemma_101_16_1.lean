module

public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap73.Lemma_73_7_3_Precoverage
public import stacks_project.Chap74.Definition_74_20_1_SmoothLocal
public import stacks_project.Chap94.«94_8_2_1_FullyFaithful»
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty
public import stacks_project.Chap101.Lemma_101_16_1_Presentation

/-!
# Checking morphisms of algebraic stacks that are smooth local on source-and-target

A morphism property of algebraic spaces that is smooth local on the
source-and-target may be checked on every smooth algebraic-space presentation
square with smooth comparison, or on some such square with surjective source
atlas. When the stacks are algebraic spaces this recovers the property on the
evaluated morphism, and when the morphism is representable by algebraic spaces
and `P` is stable under base change and fppf local on the target this recovers
`Groupoids.Hom.has`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.16.1 (1). Let `P` be a morphism property of algebraic spaces that
is smooth local on the source-and-target. For a morphism `f : X ⟶ Y` of
algebraic stacks, every 2-commutative algebraic-space square over `f` with
smooth vertical arrows whose comparison `U.toGroupoids ⟶ TwoFibreProduct.apex f b`
is smooth has `P` on the top arrow if and only if some such square with smooth
vertical arrows and surjective source atlas has `P` on the top arrow. -/
@[stacks 06FM]
theorem forallSmoothComparison_iff_existsSurjectiveSmoothSquare
    {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P] (f : X ⟶ Y) :
    forallSmoothComparison P f ↔ existsSurjectiveSmoothSquare P f :=
  sorry

/-- Lemma 101.16.1 (2). If `X` and `Y` are algebraic spaces, then the checking
conditions of Lemma 101.16.1 (1) are also equivalent to `P` holding on `f` as a
morphism of algebraic spaces, recovered by `AlgebraicSpace.toGroupoids.eval`. -/
@[stacks 06FM]
theorem forallSmoothComparison_iff_eval {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)}
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    {U V : AlgebraicSpace S} (f : U.toGroupoids ⟶ V.toGroupoids) :
    forallSmoothComparison P f ↔ P (AlgebraicSpace.toGroupoids.eval f) :=
  sorry

/-- Lemma 101.16.1 (3). If `P` is also stable under arbitrary base change and
fppf local on the target, then for a morphism `f` representable by algebraic
spaces the checking conditions of Lemma 101.16.1 (1) are equivalent to
`Groupoids.Hom.has P f` in the sense of Section 100.3. -/
@[stacks 06FM]
theorem forallSmoothComparison_iff_has {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f) :
    forallSmoothComparison P f ↔ Groupoids.Hom.has P f :=
  sorry

/-- Transport of the checking condition along presentations of algebraic stacks
by algebraic spaces recovers the property on the induced morphism of algebraic
spaces. -/
theorem forallSmoothComparison_iff_recover {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicSpace.IsSmoothLocalAtSourceAndTarget P]
    {U V : AlgebraicSpace S} (eX : X ≌ U.toGroupoids)
    (eY : Y ≌ V.toGroupoids) (f : X ⟶ Y) :
    forallSmoothComparison P f ↔
      P (AlgebraicSpace.toGroupoids.recover eX eY f) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
