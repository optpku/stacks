module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.EtaleSmoothLocal
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 101.34.1 (1): for a morphism property `P` of algebraic spaces that is
étale-smooth local on the source-and-target, and a DM morphism `f : X ⟶ Y` of
algebraic stacks, `P` holds on the top arrow of every mixed étale-smooth
algebraic-space square (`forallEtaleSmoothComparison`) if and only if it holds
for some such square with surjective source atlas
(`existsSurjectiveEtaleSmoothSquare`). The left-hand side is
`hasEtaleSmoothLocalAtSourceAndTarget P f`, identified with the existence
predicate via `hasEtaleSmoothLocalAtSourceAndTarget_def`. -/
@[stacks 0CIF] #check
  (AlgebraicGeometry.AlgebraicStack.hasEtaleSmoothLocalAtSourceAndTarget_iff_forallEtaleSmoothComparison :
    ∀ {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
      [AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P]
      {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
      (f : X ⟶ Y) [DM f],
      hasEtaleSmoothLocalAtSourceAndTarget P f ↔
        forallEtaleSmoothComparison P f)

/- Lemma 101.34.1 (2): if `X` and `Y` are representable by algebraic spaces,
then the conditions of (1) are also equivalent to `P` on the morphism recovered
along explicit representation equivalences. -/
@[stacks 0CIF] #check
  (AlgebraicGeometry.AlgebraicStack.hasEtaleSmoothLocalAtSourceAndTarget_iff_recover :
    ∀ {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
      {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
      [AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P]
      {U V : AlgebraicSpace S} (eX : X ≌ U.toGroupoids)
      (eY : Y ≌ V.toGroupoids) (f : X ⟶ Y),
      hasEtaleSmoothLocalAtSourceAndTarget P f ↔
        P (AlgebraicSpace.toGroupoids.recover eX eY f))

/- Lemma 101.34.1 (2): for the groupoid fibrations associated to algebraic
spaces, the conditions of (1) are equivalent to `P` on the evaluated morphism
of algebraic spaces. -/
@[stacks 0CIF] #check
  (AlgebraicGeometry.AlgebraicStack.hasEtaleSmoothLocalAtSourceAndTarget_iff_eval :
    ∀ {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
      [AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P]
      {U V : AlgebraicSpace S} (f : U.toGroupoids ⟶ V.toGroupoids),
      hasEtaleSmoothLocalAtSourceAndTarget P f ↔
        P (AlgebraicSpace.toGroupoids.eval f))

/- Lemma 101.34.1 (3): if `P` is also preserved under any base change and fppf
local on the base (`IsLocalAtTarget` of `fppfPrecoverage`), then for morphisms
representable by algebraic spaces this is also equivalent to
`Groupoids.Hom.has P` in the sense of Properties of Stacks, Section 100.3. -/
@[stacks 0CIF] #check
  (AlgebraicGeometry.AlgebraicStack.hasEtaleSmoothLocalAtSourceAndTarget_iff_has :
    ∀ {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
      {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
      [AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget P]
      [P.IsStableUnderBaseChange]
      [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
      {f : X ⟶ Y}, relativelyRepresentableByAlgebraicSpaces f →
        (hasEtaleSmoothLocalAtSourceAndTarget P f ↔ Groupoids.Hom.has P f))
