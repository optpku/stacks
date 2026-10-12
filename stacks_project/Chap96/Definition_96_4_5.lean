/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u w

variable {S : Scheme.{u}}
variable {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S)}
variable (f : X ⟶ Y) (τ : StandardTopology)
variable [HasSheafify (X.p.inheritedTopology (τ.overTopology S)) (Type w)]
variable [∀ P : X.totalᵒᵖ ⥤ Type w,
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]

/- Definition 96.4.5: a 1-morphism f : X ⟶ Y of categories fibred in groupoids
over (Sch/S)_fppf induces the associated morphism of topoi
(toCartesianBasedFunctor f).morphismOfTopoiIn J :
MorphismOfTopoiIn (Y.p.inheritedTopology J) (X.p.inheritedTopology J),
i.e. Sh(X_τ) ⟶ Sh(Y_τ), for J = τ.overTopology S. The displayed pair is
the inverse image f⁻¹ and pushforward f_*. The same construction applies
to the Zariski, étale, smooth, syntomic, and fppf sites. -/
@[stacks 06TT] #check
  (CategoryTheory.CartesianBasedFunctor.morphismOfTopoiIn
    (CategoryTheory.FiberedCategoryOver.Groupoids.toCartesianBasedFunctor f) (τ.overTopology S) :
    MorphismOfTopoiIn (Y.p.inheritedTopology (τ.overTopology S))
      (X.p.inheritedTopology (τ.overTopology S)))

/- Inverse image of the associated morphism: f⁻¹ : Sh(Y_τ) ⥤ Sh(X_τ). -/
@[stacks 06TT] #check
  (((toCartesianBasedFunctor f).morphismOfTopoiIn (τ.overTopology S)).inverseImage :
    Sheaf (Y.p.inheritedTopology (τ.overTopology S)) (Type w) ⥤
      Sheaf (X.p.inheritedTopology (τ.overTopology S)) (Type w))

/- Pushforward of the associated morphism: f_* : Sh(X_τ) ⥤ Sh(Y_τ). -/
@[stacks 06TT] #check
  (((toCartesianBasedFunctor f).morphismOfTopoiIn (τ.overTopology S)).pushforward :
    Sheaf (X.p.inheritedTopology (τ.overTopology S)) (Type w) ⥤
      Sheaf (Y.p.inheritedTopology (τ.overTopology S)) (Type w))
