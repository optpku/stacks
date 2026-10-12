/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.SmallToBig
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Glueing sheaves on small pro-étale sites

A sheaf on the big pro-étale site of a scheme determines a sheaf on the small
pro-étale site of every scheme over the base. This module packages the
compatible systems obtained in this way and their componentwise morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt.SmallGlueing

variable {S : Scheme.{u}}

/-- Pullback of Type-valued sheaves along base change on small pro-étale sites. -/
noncomputable def pullback {T T' : Over S} (f : T' ⟶ T) :
    Sheaf (ProEt.topology T.left) (Type (u + 1)) ⥤
      Sheaf (ProEt.topology T'.left) (Type (u + 1)) :=
  (smallProetalePullback f.left).sheafPullback (Type (u + 1))
    (ProEt.topology T.left) (ProEt.topology T'.left)

/-- Pullback along an identity is canonically isomorphic to the identity on small
pro-étale sheaves. -/
noncomputable def pullbackId (T : Over S) :
    pullback (𝟙 T) ≅ 𝟭 (Sheaf (ProEt.topology T.left) (Type (u + 1))) :=
  let siteIso : smallProetalePullback (𝟙 T.left) ≅ 𝟭 T.left.ProEt :=
    conjugateIsoEquiv
      (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ (𝟙 T.left)
        (inferInstance : WeaklyEtale (𝟙 T.left)) trivial)
      (Adjunction.id)
      (MorphismProperty.Over.mapId (P := @WeaklyEtale) (Q := ⊤) T.left).symm
  let e := Adjunction.leftAdjointIdIso
    ((smallProetalePullback (𝟙 T.left)).sheafAdjunctionContinuous (Type (u + 1))
      (ProEt.topology T.left) (ProEt.topology T.left))
    (Functor.sheafPushforwardContinuousId' siteIso
      (Type (u + 1)) (ProEt.topology T.left))
  NatIso.ofComponents (fun F ↦ e.app F) (fun _ ↦ sorry)

/-- Successive pullbacks of small pro-étale sheaves are canonically isomorphic to
pullback along the composite. -/
noncomputable def pullbackComp {T T' T'' : Over S}
    (f : T' ⟶ T) (g : T'' ⟶ T') :
    pullback f ⋙ pullback g ≅ pullback (g ≫ f) :=
  let siteIso : smallProetalePullback f.left ⋙ smallProetalePullback g.left ≅
      smallProetalePullback (g ≫ f).left :=
    (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
      g.left f.left).symm
  let e := Adjunction.leftAdjointCompIso
    ((smallProetalePullback f.left).sheafAdjunctionContinuous (Type (u + 1))
      (ProEt.topology T.left) (ProEt.topology T'.left))
    ((smallProetalePullback g.left).sheafAdjunctionContinuous (Type (u + 1))
      (ProEt.topology T'.left) (ProEt.topology T''.left))
    ((smallProetalePullback (g ≫ f).left).sheafAdjunctionContinuous (Type (u + 1))
      (ProEt.topology T.left) (ProEt.topology T''.left))
    (Functor.sheafPushforwardContinuousComp' siteIso
      (Type (u + 1)) (ProEt.topology T.left) (ProEt.topology T'.left)
        (ProEt.topology T''.left))
  NatIso.ofComponents (fun F ↦ e.app F) (fun _ ↦ sorry)

/-- A compatible system of sheaves on the small pro-étale sites of schemes over a
fixed base. -/
structure Object (S : Scheme.{u}) where
  /-- The sheaf on the small pro-étale site of a scheme over the base. -/
  obj (T : Over S) : Sheaf (ProEt.topology T.left) (Type (u + 1))
  /-- The comparison from pullback of the sheaf over the target to the sheaf over
the source. -/
  transition {T T' : Over S} (f : T' ⟶ T) : (pullback f).obj (obj T) ⟶ obj T'
  /-- The transition along an identity is the canonical identity comparison. -/
  transition_id (T : Over S) :
    transition (𝟙 T) = (pullbackId T).hom.app (obj T)
  /-- Transition maps satisfy the pullback cocycle condition. -/
  transition_comp {T T' T'' : Over S} (f : T' ⟶ T) (g : T'' ⟶ T') :
    CommSq ((pullbackComp f g).hom.app (obj T)) ((pullback g).map (transition f))
      (transition (g ≫ f)) (transition g)
  /-- A transition along a weakly étale morphism is invertible. -/
  transition_isIso {T T' : Over S} (f : T' ⟶ T) (hf : WeaklyEtale f.left) :
    IsIso (transition f)

namespace Object

/-- The fields of a compatible small pro-étale system express identity,
composition, and weakly étale invertibility of its transition maps. -/
theorem spec (F : Object S) :
    (∀ T : Over S, F.transition (𝟙 T) = (pullbackId T).hom.app (F.obj T)) ∧
      (∀ {T T' T'' : Over S} (f : T' ⟶ T) (g : T'' ⟶ T'),
        CommSq ((pullbackComp f g).hom.app (F.obj T))
          ((pullback g).map (F.transition f)) (F.transition (g ≫ f))
          (F.transition g)) ∧
      (∀ {T T' : Over S} (f : T' ⟶ T) (hf : WeaklyEtale f.left),
        IsIso (F.transition f)) := sorry

end Object

/-- A morphism of compatible small pro-étale systems is a componentwise sheaf
morphism commuting with every transition map. -/
@[ext]
structure Hom (F G : Object S) where
  /-- The component over a scheme above the base. -/
  app (T : Over S) : F.obj T ⟶ G.obj T
  /-- Component maps commute with pullback transitions. -/
  naturality {T T' : Over S} (f : T' ⟶ T) :
    CommSq ((pullback f).map (app T)) (F.transition f) (G.transition f) (app T')

namespace Hom

/-- The identity compatible morphism. -/
def id (F : Object S) : Hom F F where
  app T := 𝟙 (F.obj T)
  naturality _ := sorry

/-- Composition of compatible morphisms. -/
def comp {F G H : Object S} (α : Hom F G) (β : Hom G H) : Hom F H where
  app T := α.app T ≫ β.app T
  naturality _ := sorry

/-- Composition with the identity on the source leaves a compatible morphism unchanged. -/
theorem id_comp {F G : Object S} (α : Hom F G) : comp (id F) α = α := sorry

/-- Composition with the identity on the target leaves a compatible morphism unchanged. -/
theorem comp_id {F G : Object S} (α : Hom F G) : comp α (id G) = α := sorry

/-- Composition of compatible morphisms is associative. -/
theorem assoc {F G H I : Object S} (α : Hom F G) (β : Hom G H) (γ : Hom H I) :
    comp (comp α β) γ = comp α (comp β γ) := sorry

end Hom

/-- The category of compatible systems, bundled without installing a global
category instance on the explicit object structure. -/
noncomputable def category (S : Scheme.{u}) : Cat :=
  { α := Object S
    str :=
      { Hom := Hom
        id := Hom.id
        comp := Hom.comp
        id_comp := Hom.id_comp
        comp_id := Hom.comp_id
        assoc := Hom.assoc } }

set_option backward.privateInPublic true in
/-- The compatibility equation for the projection from a pullback object over a
scheme to the corresponding object over the base. -/
private theorem fromSheafProjection_over
    {T T' : Over S} (f : T' ⟶ T) (U : T.left.ProEtᵒᵖ) :
    pullback.fst U.unop.hom f.left ≫ U.unop.hom ≫ T.hom =
      pullback.snd U.unop.hom f.left ≫ T'.hom := sorry

set_option backward.privateInPublic true in
/-- The map adjoint to the canonical transition from a big pro-étale sheaf,
expressed through direct small-site base change. -/
noncomputable def fromSheafTransitionAdjoint
    (𝒢 : Sheaf (proetaleTopology.{u}.over S) (Type (u + 1)))
    {T T' : Over S} (f : T' ⟶ T) :
    (SmallToBig.inverseImage T.hom).obj 𝒢 ⟶
      ((smallProetalePullback f.left).sheafPushforwardContinuous (Type (u + 1))
        (ProEt.topology T.left) (ProEt.topology T'.left)).obj
          ((SmallToBig.inverseImage T'.hom).obj 𝒢) :=
  ObjectProperty.homMk
    { app := fun U ↦
        𝒢.1.map
          (Over.homMk (pullback.fst U.unop.hom f.left)
            (fromSheafProjection_over f U) :
            (SmallToBig.relocalizationFunctor T'.hom).obj
                ((smallProetalePullback f.left).obj U.unop) ⟶
              (SmallToBig.relocalizationFunctor T.hom).obj U.unop).op
      naturality := sorry }

/-- The canonical transition of the compatible system associated with a big
pro-étale sheaf. -/
noncomputable def fromSheafTransition
    (𝒢 : Sheaf (proetaleTopology.{u}.over S) (Type (u + 1)))
    {T T' : Over S} (f : T' ⟶ T) :
    (pullback f).obj ((SmallToBig.inverseImage T.hom).obj 𝒢) ⟶
      (SmallToBig.inverseImage T'.hom).obj 𝒢 :=
  ((smallProetalePullback f.left).sheafAdjunctionContinuous (Type (u + 1))
    (ProEt.topology T.left) (ProEt.topology T'.left)).homEquiv _ _ |>.symm
      (fromSheafTransitionAdjoint 𝒢 f)

set_option backward.privateInPublic true in
/-- The identity transition of the system associated with a big pro-étale sheaf. -/
private theorem fromSheafTransition_id
    (𝒢 : Sheaf (proetaleTopology.{u}.over S) (Type (u + 1))) (T : Over S) :
    fromSheafTransition 𝒢 (𝟙 T) =
      (pullbackId T).hom.app ((SmallToBig.inverseImage T.hom).obj 𝒢) := sorry

set_option backward.privateInPublic true in
/-- The composite transition of the system associated with a big pro-étale sheaf
satisfies the pullback cocycle condition. -/
private theorem fromSheafTransition_comp
    (𝒢 : Sheaf (proetaleTopology.{u}.over S) (Type (u + 1)))
    {T T' T'' : Over S} (f : T' ⟶ T) (g : T'' ⟶ T') :
    CommSq ((pullbackComp f g).hom.app ((SmallToBig.inverseImage T.hom).obj 𝒢))
      ((pullback g).map (fromSheafTransition 𝒢 f))
      (fromSheafTransition 𝒢 (g ≫ f)) (fromSheafTransition 𝒢 g) := sorry

set_option backward.privateInPublic true in
/-- The transition of the system associated with a big pro-étale sheaf is
invertible along weakly étale morphisms. -/
private theorem fromSheafTransition_isIso
    (𝒢 : Sheaf (proetaleTopology.{u}.over S) (Type (u + 1)))
    {T T' : Over S} (f : T' ⟶ T) (hf : WeaklyEtale f.left) :
    IsIso (fromSheafTransition 𝒢 f) := sorry

namespace Object

set_option backward.privateInPublic true in
/-- The compatible system of small pro-étale sheaves obtained by restricting a
big pro-étale sheaf. -/
noncomputable def ofSheaf
    (𝒢 : Sheaf (proetaleTopology.{u}.over S) (Type (u + 1))) : Object S where
  obj T := (SmallToBig.inverseImage T.hom).obj 𝒢
  transition f := fromSheafTransition 𝒢 f
  transition_id T := fromSheafTransition_id 𝒢 T
  transition_comp f g := fromSheafTransition_comp 𝒢 f g
  transition_isIso f hf := fromSheafTransition_isIso 𝒢 f hf

end Object

/-- A morphism of big pro-étale sheaves induces the componentwise compatible
morphism between their small pro-étale systems. -/
noncomputable def fromSheafMap
    {𝒢 ℋ : Sheaf (proetaleTopology.{u}.over S) (Type (u + 1))} (η : 𝒢 ⟶ ℋ) :
    Hom (Object.ofSheaf 𝒢) (Object.ofSheaf ℋ) where
  app T := (SmallToBig.inverseImage T.hom).map η
  naturality _ := sorry

set_option backward.privateInPublic true in
/-- The identity map of a big pro-étale sheaf induces the identity compatible
morphism. -/
private theorem fromSheaf_map_id
    (𝒢 : Sheaf (proetaleTopology.{u}.over S) (Type (u + 1))) :
    fromSheafMap (𝟙 𝒢) = Hom.id (Object.ofSheaf 𝒢) := sorry

set_option backward.privateInPublic true in
/-- The composite of maps of big pro-étale sheaves induces the composite
compatible morphism. -/
private theorem fromSheaf_map_comp
    {𝒢 ℋ 𝒦 : Sheaf (proetaleTopology.{u}.over S) (Type (u + 1))}
    (η : 𝒢 ⟶ ℋ) (θ : ℋ ⟶ 𝒦) :
    fromSheafMap (η ≫ θ) = Hom.comp (fromSheafMap η) (fromSheafMap θ) := sorry

set_option backward.privateInPublic true in
/-- Restriction of big pro-étale sheaves to their compatible systems on all
small pro-étale sites. -/
noncomputable def fromSheaf (S : Scheme.{u}) :
    Sheaf (proetaleTopology.{u}.over S) (Type (u + 1)) ⥤ category S where
  obj := Object.ofSheaf
  map := fromSheafMap
  map_id := fromSheaf_map_id
  map_comp := fromSheaf_map_comp

/-- Restriction from the big pro-étale site to compatible sheaves on all small
pro-étale sites is an equivalence of categories. -/
instance fromSheaf_isEquivalence (S : Scheme.{u}) :
    Functor.IsEquivalence (fromSheaf S) := sorry

end AlgebraicGeometry.Scheme.ProEt.SmallGlueing
