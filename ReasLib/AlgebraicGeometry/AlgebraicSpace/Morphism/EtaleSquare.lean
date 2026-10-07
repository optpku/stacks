module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A property of scheme morphisms holds étale locally on both sides of a
commuting square of algebraic spaces when it holds for the induced scheme
morphism in every such square. -/
def etaleLocally {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  ∀ {U V : Over S} (sourceChart : yoneda.obj U ⟶ X.functorOfPoints)
    (targetChart : yoneda.obj V ⟶ Y.functorOfPoints) (chartMap : U ⟶ V),
    MorphismProperty.presheaf (MorphismProperty.over (@AlgebraicGeometry.Etale)) sourceChart →
      MorphismProperty.presheaf (MorphismProperty.over (@AlgebraicGeometry.Etale)) targetChart →
        sourceChart ≫ f = yoneda.map chartMap ≫ targetChart → P chartMap.left

/-- The definition of `etaleLocally` is equivalent to its expanded
quantified form. -/
theorem etaleLocally_iff {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    etaleLocally P f ↔
      ∀ {U V : Over S} (sourceChart : yoneda.obj U ⟶ X.functorOfPoints)
        (targetChart : yoneda.obj V ⟶ Y.functorOfPoints) (chartMap : U ⟶ V),
        MorphismProperty.presheaf (MorphismProperty.over (@AlgebraicGeometry.Etale))
            sourceChart →
          MorphismProperty.presheaf (MorphismProperty.over (@AlgebraicGeometry.Etale))
            targetChart →
            sourceChart ≫ f = yoneda.map chartMap ≫ targetChart → P chartMap.left :=
  Iff.rfl

namespace etaleLocally

/-- Apply an étale-local property to a commuting square with étale charts. -/
theorem apply {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} (h : etaleLocally P f)
    {U V : Over S} (sourceChart : yoneda.obj U ⟶ X.functorOfPoints)
    (targetChart : yoneda.obj V ⟶ Y.functorOfPoints) (chartMap : U ⟶ V)
    (hsource :
      MorphismProperty.presheaf (MorphismProperty.over (@AlgebraicGeometry.Etale)) sourceChart)
    (htarget :
      MorphismProperty.presheaf (MorphismProperty.over (@AlgebraicGeometry.Etale)) targetChart)
    (w : sourceChart ≫ f = yoneda.map chartMap ≫ targetChart) : P chartMap.left :=
  h sourceChart targetChart chartMap hsource htarget w

end etaleLocally

end AlgebraicGeometry.AlgebraicSpace
