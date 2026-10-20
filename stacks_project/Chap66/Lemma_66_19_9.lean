/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.InverseImage.Exact
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.InverseImage.Stalk
import StacksCheckRecall

/-!
# Lemma 66.19.9

Inverse image along `f_small` is exact on abelian sheaves and on sheaves of sets, sends
sheafified representables to sheafified representables of fibre products, and identifies
stalks at geometric points with stalks at the image geometric point.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint

universe u

section ExactAb

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/- Lemma 66.19.9 (1): the functor `f_small⁻¹ : Ab(Y_étale) → Ab(X_étale)` is exact. -/
@[stacks 04K2] #check
  (AlgebraicGeometry.AlgebraicSpace.smallEtaleInverseImage_exact_addCommGrp f :
    exactFunctor (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})
      (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
      (sheafInverseImage AddCommGrpCat.{u + 1} f))

end ExactAb

section ExactType

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/- Lemma 66.19.9 (2): the functor `f_small⁻¹ : Sh(Y_étale) → Sh(X_étale)` is exact, i.e. it
commutes with finite limits and finite colimits, see Categories, Definition 4.23.1. -/
@[stacks 04K2] #check
  (AlgebraicGeometry.AlgebraicSpace.smallEtaleInverseImage_exact_type f :
    exactFunctor (Sheaf (smallEtaleTopology Y) (Type (u + 1)))
      (Sheaf (smallEtaleTopology X) (Type (u + 1)))
      (smallEtaleMorphismOfTopoi f).inverseImage)

end ExactType

section Representable

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable (V : spacesEtaleSite Y)

/- Lemma 66.19.9 (3): for any étale morphism `V → Y` of algebraic spaces one has
`f_small⁻¹ h_V = h_{X ×_Y V}`, as sheaves on the étale sites of algebraic spaces, equivalently
on the small étale sites via Lemma 66.18.3. -/
@[stacks 04K2] #check
  (CategoryTheory.Functor.SheafifiedRepresentable.pullbackIso.{u + 1, u + 1, u + 1, u + 1, u + 1}
      (spacesEtalePullback f) (spacesEtaleTopology Y) (spacesEtaleTopology X) V :
    (spacesEtaleTopology X).uliftSheafifiedRepresentable.{u + 1, u + 1, u + 1}
        ((spacesEtalePullback f).obj V) ≅
      ((spacesEtalePullback f).sheafPullback (Type (u + 1))
        (spacesEtaleTopology Y) (spacesEtaleTopology X)).obj
        ((spacesEtaleTopology Y).uliftSheafifiedRepresentable.{u + 1, u + 1, u + 1} V))

end Representable

section Stalk

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable (xbar : GeometricPoint X)
variable (G : Sheaf (smallEtaleTopology Y) (Type (u + 1)))

/- Lemma 66.19.9 (4): there is a canonical identification `(f_small⁻¹ G)_x̄ ≅ G_ȳ` where
`ȳ = f ∘ x̄`. -/
@[stacks 04K2] #check
  (AlgebraicGeometry.AlgebraicSpace.smallEtaleInverseImage_stalkIso f xbar G :
    (toSmallEtalePoint xbar).sheafFiber.obj
        ((smallEtaleMorphismOfTopoi f).inverseImage.obj G) ≅
      (toSmallEtalePoint (xbar.map f)).sheafFiber.obj G)

end Stalk
