module

public import stacks_project.Chap78.Lemma_78_17_1_Restriction
public import stacks_project.Chap78.Lemma_78_17_1_Presentation
public import stacks_project.Chap78.Lemma_78_17_1_Points
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 78.17.1 (1): restriction along `g : U' ⟶ U` gives a groupoid in algebraic spaces
whose composition is induced canonically from the original composition. -/
@[stacks 044B] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.pullback :
    {S : AlgebraicGeometry.Scheme.{u}} → {B : AlgebraicGeometry.AlgebraicSpace S} →
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B) →
      {U' : Over B} → (g : U' ⟶ G.U) →
        AlgebraicGeometry.GroupoidAlgebraicSpace B)

/- Companion recall: `AlgebraicGeometry.GroupoidAlgebraicSpace.pullback_c G g` identifies
the restricted composition with the canonical pullback composition. -/
#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.pullback_c :
    {S : AlgebraicGeometry.Scheme.{u}} → {B : AlgebraicGeometry.AlgebraicSpace S} →
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B) →
      {U' : Over B} → (g : U' ⟶ G.U) →
        (AlgebraicGeometry.GroupoidAlgebraicSpace.pullback G g).c =
          AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackComposition G g)

/- Companion recall: the restricted arrow space has the iterated fibre-product presentation
from the two displayed pullback squares. -/
#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackArrowIso :
    {S : AlgebraicGeometry.Scheme.{u}} → {B : AlgebraicGeometry.AlgebraicSpace S} →
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B) →
      {U' : Over B} → (g : U' ⟶ G.U) →
        (G.toPreRelation.pullback g).left ≅
          AlgebraicGeometry.GroupoidAlgebraicSpace.iteratedPullbackArrows G g)

/- Lemma 78.17.1 (2): the projections from the restricted object and arrow spaces define a
morphism to the original groupoid in algebraic spaces. -/
@[stacks 044B] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackHom :
    {S : AlgebraicGeometry.Scheme.{u}} → {B : AlgebraicGeometry.AlgebraicSpace S} →
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B) →
      {U' : Over B} → (g : U' ⟶ G.U) →
        AlgebraicGeometry.GroupoidAlgebraicSpace.Hom
          (AlgebraicGeometry.GroupoidAlgebraicSpace.pullback G g) G)

/- Lemma 78.17.1 (3): on every scheme of points over `B`, the canonical functor identifies
with the restriction of the original groupoid along the induced object map. -/
@[stacks 044B] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.pointsPullbackEquivalence_comp :
    {S : AlgebraicGeometry.Scheme.{u}} → {B : AlgebraicGeometry.AlgebraicSpace S} →
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B) →
      {U' : Over B} → (g : U' ⟶ G.U) → {T : Over S} →
        (σ : AlgebraicGeometry.AlgebraicSpace.ofOver T ⟶ B) →
          (AlgebraicGeometry.GroupoidAlgebraicSpace.pointsPullbackEquivalence G g σ).functor ⋙
              CategoryTheory.inducedFunctor
                (AlgebraicGeometry.GroupoidAlgebraicSpace.restrictionObjectMap G g σ) =
            (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackHom G g).mapPoints σ)
