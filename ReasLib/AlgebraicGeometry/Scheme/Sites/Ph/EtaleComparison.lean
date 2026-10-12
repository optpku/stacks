/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CatCommSq
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Big
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Big
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig

@[expose] public section

open CategoryTheory
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PhComparison

/-- The comparison from big ph sheaves to big étale sheaves commutes with
direct image along a morphism of schemes over a fixed base. -/
theorem bigPhEtaleCommSq {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    Nonempty (CatCommSq (Ph.Big.morphismOfTopoi f.left).pushforward
      (standardComparison .etale X.left).pushforward (standardComparison .etale Y.left).pushforward
      (Etale.Big.morphismOfTopoi f.left).pushforward) := sorry

/-- The composite comparison from big ph sheaves to small étale sheaves
commutes with direct image along a morphism of schemes over a fixed base. -/
theorem phSmallEtaleCommSq {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    Nonempty (CatCommSq (Ph.Big.morphismOfTopoi f.left).pushforward
      ((standardComparison .etale X.left).pushforward ⋙
        (Etale.SmallToBig.siteMorphismOfTopoi X.left).pushforward)
      ((standardComparison .etale Y.left).pushforward ⋙
        (Etale.SmallToBig.siteMorphismOfTopoi Y.left).pushforward)
      (Etale.SmallToBig.smallMorphism f.left).pushforward) := sorry

end AlgebraicGeometry.Scheme.PhComparison

end

end
