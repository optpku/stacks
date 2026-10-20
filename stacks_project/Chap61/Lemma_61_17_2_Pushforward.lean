module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Pushforward

/-!
# Abelian small and big pro-étale pushforwards

Direct image of abelian sheaves along a morphism of schemes, on the small
pro-étale site and on the big slice site, together with the cartesian
small-to-big comparison.
-/

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/- Lemma 61.17.2. Abelian direct images on the small and big pro-étale sites. -/
#check (AlgebraicGeometry.Scheme.ProEt.smallPushforward :
  ∀ {S T : Scheme.{u}}, (T ⟶ S) →
    Sheaf (topology T) AddCommGrpCat.{u + 1} ⥤
      Sheaf (topology S) AddCommGrpCat.{u + 1})

#check (AlgebraicGeometry.Scheme.ProEt.bigPushforward :
  ∀ {S T : Scheme.{u}} (f : T ⟶ S) [HasPullbacksAlong f],
    Sheaf (proetaleTopology.over T) AddCommGrpCat.{u + 1} ⥤
      Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1})

end AlgebraicGeometry.Scheme.ProEt
