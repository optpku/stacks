module

public import Mathlib.CategoryTheory.CatCommSq
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Big
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Fppf

/-- The direct images for the big fppf and big étale morphisms form a
commutative square under the étale-to-fppf comparison morphisms. -/
theorem bigEtaleCommSq {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    Nonempty (CatCommSq
      (Fppf.Big.morphismOfTopoi f.left).pushforward
      (AlgebraicGeometry.StandardTopology.toFppf .etale X.left).pushforward
      (AlgebraicGeometry.StandardTopology.toFppf .etale Y.left).pushforward
      (Etale.Big.morphismOfTopoi f.left).pushforward) := sorry

/-- The direct images for the small étale morphism and the big fppf-to-étale
comparison form a commutative square after passage from the small to the big
étale site. -/
theorem smallEtaleCommSq {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    Nonempty (CatCommSq
      (Fppf.Big.morphismOfTopoi f.left).pushforward
      ((AlgebraicGeometry.StandardTopology.toFppf .etale X.left).pushforward ⋙
        (Etale.SmallToBig.siteMorphismOfTopoi X.left).pushforward)
      ((AlgebraicGeometry.StandardTopology.toFppf .etale Y.left).pushforward ⋙
        (Etale.SmallToBig.siteMorphismOfTopoi Y.left).pushforward)
      (Etale.SmallToBig.smallMorphism f.left).pushforward) := sorry

end AlgebraicGeometry.Scheme.Fppf

end

end
