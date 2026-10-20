module

public import Mathlib.CategoryTheory.CatCommSq
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.Big
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.BigTopos
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesTopos

/-!
# Naturality of fppf and étale comparisons

The comparisons from big fppf topoi to big and small étale topoi commute
with morphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Fppf

/-- Direct images for the big fppf and big étale morphisms form a commutative
square with the identity-induced comparison morphisms. -/
theorem bigEtaleCommSq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Nonempty (CatCommSq
      (CategoryTheory.Over.Site.morphismOfTopoi.{u + 1, u + 1, u + 1}
        (fppfTopology S) f).pushforward
      (epsilon X).pushforward
      (epsilon Y).pushforward
      (Etale.Big.morphismOfTopoi f).pushforward) := sorry

/-- Direct images for the big fppf and small étale morphisms form a commutative
square with the comparisons obtained by composing the big fppf-to-étale and
big-to-small étale morphisms. -/
theorem smallEtaleCommSq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Nonempty (CatCommSq
      (CategoryTheory.Over.Site.morphismOfTopoi.{u + 1, u + 1, u + 1}
        (fppfTopology S) f).pushforward
      (Etale.SmallToBig.fppfComparison X).pushforward
      (Etale.SmallToBig.fppfComparison Y).pushforward
      (smallEtaleMorphismOfTopoi f).pushforward) := sorry

end AlgebraicGeometry.AlgebraicSpace.Fppf

end

end
