module

import Mathlib.Tactic.CrossRefAttribute

-- Import decisions:
-- * `Map` owns the square induced by a morphism into the canonical two-fibre product.
-- * `Target` owns the square induced directly by a pseudo-pullback cone.
--   The comparison here only assembles their two leg isomorphisms.
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.Comparison.Map
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.Comparison.Target

/-!
# Comparison isomorphism for relative representability

This leaf assembles the two explicit leg comparisons into the canonical natural isomorphism from
the map induced by a cone morphism to the ordinary categorical-pullback target of that cone.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Bicategory
open CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback
open scoped Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids.PseudoPullbackComparison

section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The left-leg isomorphism comparing the map induced by u with the target attached to P. -/
@[stacks 0H2E "left leg of the pseudo-pullback comparison"]
noncomputable def fstIso
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection}
    (u : P ⟶
      CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection) :
    (map.square (PseudoPullbackCone.map u)).fst ≅
      (target.square P).fst :=
  map.square.fstIso (PseudoPullbackCone.map u) ≪≫
    FiberedCategoryOver.Groupoids.toFunctorIso (PseudoPullbackCone.fstIso u) ≪≫
      (target.square.fstIso P).symm

/-- The right-leg isomorphism comparing the map induced by u with the target attached to P. -/
@[stacks 0H2E "right leg of the pseudo-pullback comparison"]
noncomputable def sndIso
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection}
    (u : P ⟶
      CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection) :
    (map.square (PseudoPullbackCone.map u)).snd ≅
      (target.square P).snd :=
  map.square.sndIso (PseudoPullbackCone.map u) ≪≫
    FiberedCategoryOver.Groupoids.toFunctorIso (PseudoPullbackCone.sndIso u) ≪≫
      (target.square.sndIso P).symm

namespace fstIso

/-- The forward component of the left-leg comparison is the composite of the map-square,
cone-morphism, and target-square comparison components. -/
@[simp]
theorem hom.app
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection}
    (u : P ⟶
      CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection)
    (a : P.pt.total) :
    (fstIso u).hom.app a =
      (map.square.fstIso (PseudoPullbackCone.map u)).hom.app a ≫
        (FiberedCategoryOver.Groupoids.toFunctorIso
          (PseudoPullbackCone.fstIso u)).hom.app a ≫
          (target.square.fstIso P).inv.app a := sorry

/-- The inverse component of the left-leg comparison is the reverse composite of the
target-square, cone-morphism, and map-square comparison components. -/
@[simp]
theorem inv.app
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection}
    (u : P ⟶
      CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection)
    (a : P.pt.total) :
    (fstIso u).inv.app a =
      (target.square.fstIso P).hom.app a ≫
        (FiberedCategoryOver.Groupoids.toFunctorIso
          (PseudoPullbackCone.fstIso u)).inv.app a ≫
          (map.square.fstIso (PseudoPullbackCone.map u)).inv.app a := sorry

end fstIso

namespace sndIso

/-- The forward component of the right-leg comparison is the composite of the map-square,
cone-morphism, and target-square comparison components. -/
@[simp]
theorem hom.app
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection}
    (u : P ⟶
      CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection)
    (a : P.pt.total) :
    (sndIso u).hom.app a =
      (map.square.sndIso (PseudoPullbackCone.map u)).hom.app a ≫
        (FiberedCategoryOver.Groupoids.toFunctorIso
          (PseudoPullbackCone.sndIso u)).hom.app a ≫
          (target.square.sndIso P).inv.app a := sorry

/-- The inverse component of the right-leg comparison is the reverse composite of the
target-square, cone-morphism, and map-square comparison components. -/
@[simp]
theorem inv.app
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection}
    (u : P ⟶
      CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection)
    (a : P.pt.total) :
    (sndIso u).inv.app a =
      (target.square.sndIso P).hom.app a ≫
        (FiberedCategoryOver.Groupoids.toFunctorIso
          (PseudoPullbackCone.sndIso u)).inv.app a ≫
          (map.square.sndIso (PseudoPullbackCone.map u)).inv.app a := sorry

end sndIso

namespace Implementation

/-- The transported leg isomorphisms satisfy the coherence required by
CategoricalPullback.mkNatIso.

Proof strategy: unfold the two square owners. Their structural isomorphisms are the
associator/whiskering composites in CategoricalPullback.mkNatIso; the two leg cells of
PseudoPullbackCone.fac u identify the remaining components. -/
private theorem legsCompatible
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection}
    (u : P ⟶
      CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection) :
    Functor.whiskerRight (fstIso u).hom X.p ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft (target P)
            (CatCommSq.iso (π₁ X.p X.p) (π₂ X.p X.p) X.p X.p).hom ≫
          (Functor.associator _ _ _).inv =
      (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft (map (PseudoPullbackCone.map u))
            (CatCommSq.iso (π₁ X.p X.p) (π₂ X.p X.p) X.p X.p).hom ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (sndIso u).hom X.p := sorry

end Implementation

/-- The canonical comparison isomorphism from the map induced by u to the ordinary
categorical-pullback functor attached to P. Both sides land in X.p ⊡ X.p; the implementation
ULift is confined to BaseProjection.pullbackDown. -/
@[stacks 0H2E "comparison from a pseudo-pullback cone to its categorical pullback"]
noncomputable def iso
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection}
    (u : P ⟶
      CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection) :
    map (PseudoPullbackCone.map u) ≅
      target P :=
  CategoricalPullback.mkNatIso
    (fstIso u)
    (sndIso u)
    (coh := Implementation.legsCompatible u)

/-- The first component of the forward comparison is the forward left-leg comparison. -/
@[simp]
theorem iso.hom.app.fst
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection}
    (u : P ⟶
      CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection)
    (a : P.pt.total) :
    ((iso u).hom.app a).fst = (fstIso u).hom.app a := sorry

/-- The second component of the forward comparison is the forward right-leg comparison. -/
@[simp]
theorem iso.hom.app.snd
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection}
    (u : P ⟶
      CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection)
    (a : P.pt.total) :
    ((iso u).hom.app a).snd = (sndIso u).hom.app a := sorry

/-- The first component of the inverse comparison is the inverse left-leg comparison. -/
@[simp]
theorem iso.inv.app.fst
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection}
    (u : P ⟶
      CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection)
    (a : P.pt.total) :
    ((iso u).inv.app a).fst = (fstIso u).inv.app a := sorry

/-- The second component of the inverse comparison is the inverse right-leg comparison. -/
@[simp]
theorem iso.inv.app.snd
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection}
    (u : P ⟶
      CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection)
    (a : P.pt.total) :
    ((iso u).inv.app a).snd = (sndIso u).inv.app a := sorry

end

end FiberedCategoryOver.Groupoids.PseudoPullbackComparison

end CategoryTheory
