/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Sites.Presheaf.InverseImage
public import stacks_project.Chap96.Definition_96_4_1_AssociatedTopology
public import stacks_project.Chap96.Definition_96_4_3_Sheaf

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor FiberedCategoryOver.Groupoids
open AlgebraicGeometry.FiberedInGroupoids
open scoped Bicategory

universe u w

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)

/-- Lemma 96.4.4 (1): Let `f : X ⟶ Y` be a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`, and let `τ` be one of the standard topologies
Zariski, étale, smooth, syntomic, or fppf. The presheaf inverse image `f^p` of
96.3.1.1, namely `presheafInverseImage (toFunctor f) (Type w)`, sends `τ`-sheaves
on `Y` to `τ`-sheaves on `X`. -/
@[stacks 06TS]
theorem presheafInverseImage_isSheafFor {G : Y.totalᵒᵖ ⥤ Type w}
    (hG : IsSheafFor Y.p τ G) :
    IsSheafFor X.p τ ((presheafInverseImage (toFunctor f) (Type w)).obj G) :=
  sorry

/-- Lemma 96.4.4 (2): Let `f : X ⟶ Y` be a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`, and let `τ` be one of the standard topologies
Zariski, étale, smooth, syntomic, or fppf. The presheaf pushforward `_p f` of
96.3.1.1, namely right Kan extension along `(toFunctor f).op`, sends `τ`-sheaves
on `X` to `τ`-sheaves on `Y`. -/
@[stacks 06TS]
theorem presheafRan_isSheafFor
    [∀ P : X.totalᵒᵖ ⥤ Type w, HasRightKanExtension (toFunctor f).op P]
    {F : X.totalᵒᵖ ⥤ Type w} (hF : IsSheafFor X.p τ F) :
    IsSheafFor Y.p τ ((toFunctor f).op.ran.obj F) :=
  sorry

#check CartesianBasedFunctor.inheritedTopology.isContinuous
  (toCartesianBasedFunctor f) (τ.overTopology S)
#check CartesianBasedFunctor.inheritedTopology.isCocontinuous
  (toCartesianBasedFunctor f) (τ.overTopology S)

variable [HasSheafify (X.associatedTopology τ) (Type w)]
variable [∀ P : X.totalᵒᵖ ⥤ Type w,
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]

/- Lemma 96.4.4 (3): the same functors define a morphism of topoi
`f : Sh(X_τ) ⟶ Sh(Y_τ)`, namely
`(toCartesianBasedFunctor f).morphismOfTopoiIn (τ.overTopology S)` as a
`MorphismOfTopoiIn (Y.associatedTopology τ) (X.associatedTopology τ)`. -/
@[stacks 06TS] #check
  ((toCartesianBasedFunctor f).morphismOfTopoiIn (τ.overTopology S) :
    MorphismOfTopoiIn (Y.associatedTopology τ) (X.associatedTopology τ))

#check CartesianBasedFunctor.morphismOfTopoiIn.pushforward_eq
#check CartesianBasedFunctor.morphismOfTopoiIn.inverseImage_eq
#check CartesianBasedFunctor.morphismOfTopoiIn.inverseImageComparison

end AlgebraicGeometry.GroupoidsOver
