/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-!
# Glueing sheaves on small étale sites

A sheaf on the big étale site of a scheme determines a sheaf on the small
étale site of every scheme over the base. This module packages the compatible
systems obtained in this way and their componentwise morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.SmallGlueing

variable {S : Scheme.{u}}

/-- Pullback of Type-valued sheaves along base change on small étale sites. -/
noncomputable def pullback {T T' : Over S} (f : T' ⟶ T) :
    Sheaf T.left.smallEtaleTopology (Type (u + 1)) ⥤
      Sheaf T'.left.smallEtaleTopology (Type (u + 1)) :=
  (smallEtalePullback f.left).sheafPullback (Type (u + 1))
    T.left.smallEtaleTopology T'.left.smallEtaleTopology

/-- Pullback along an identity is canonically isomorphic to the identity on small étale sheaves. -/
noncomputable def pullbackId (T : Over S) :
    pullback (𝟙 T) ≅ 𝟭 (Sheaf T.left.smallEtaleTopology (Type (u + 1))) :=
  let siteIso : smallEtalePullback (𝟙 T.left) ≅ 𝟭 T.left.Etale :=
    conjugateIsoEquiv
      (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ (𝟙 T.left)
        (inferInstance : Etale (𝟙 T.left)) trivial)
      (Adjunction.id)
      (MorphismProperty.Over.mapId (P := @Etale) (Q := ⊤) T.left).symm
  let e := Adjunction.leftAdjointIdIso
    ((smallEtalePullback (𝟙 T.left)).sheafAdjunctionContinuous (Type (u + 1))
      T.left.smallEtaleTopology T.left.smallEtaleTopology)
    (Functor.sheafPushforwardContinuousId' siteIso
      (Type (u + 1)) T.left.smallEtaleTopology)
  NatIso.ofComponents (fun F ↦ e.app F) (fun _ ↦ sorry)

/-- Successive pullbacks of small étale sheaves are canonically isomorphic to pullback along the
composite. -/
noncomputable def pullbackComp {T T' T'' : Over S}
    (f : T' ⟶ T) (g : T'' ⟶ T') :
    pullback f ⋙ pullback g ≅ pullback (g ≫ f) :=
  let siteIso : smallEtalePullback f.left ⋙ smallEtalePullback g.left ≅
      smallEtalePullback (g ≫ f).left :=
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g.left f.left).symm
  let e := Adjunction.leftAdjointCompIso
    ((smallEtalePullback f.left).sheafAdjunctionContinuous (Type (u + 1))
      T.left.smallEtaleTopology T'.left.smallEtaleTopology)
    ((smallEtalePullback g.left).sheafAdjunctionContinuous (Type (u + 1))
      T'.left.smallEtaleTopology T''.left.smallEtaleTopology)
    ((smallEtalePullback (g ≫ f).left).sheafAdjunctionContinuous (Type (u + 1))
      T.left.smallEtaleTopology T''.left.smallEtaleTopology)
    (Functor.sheafPushforwardContinuousComp' siteIso
      (Type (u + 1)) T.left.smallEtaleTopology T'.left.smallEtaleTopology
        T''.left.smallEtaleTopology)
  NatIso.ofComponents (fun F ↦ e.app F) (fun _ ↦ sorry)

/-- A compatible system of sheaves on the small étale sites of schemes over a fixed base. -/
structure Object (S : Scheme.{u}) where
  /-- The sheaf on the small étale site of a scheme over the base. -/
  obj (T : Over S) : Sheaf T.left.smallEtaleTopology (Type (u + 1))
  /-- The comparison from pullback of the sheaf over the target to the sheaf over the source. -/
  transition {T T' : Over S} (f : T' ⟶ T) : (pullback f).obj (obj T) ⟶ obj T'
  /-- The transition along an identity is the canonical identity comparison. -/
  transition_id (T : Over S) : transition (𝟙 T) = (pullbackId T).hom.app (obj T)
  /-- Transition maps satisfy the pullback cocycle condition. -/
  transition_comp {T T' T'' : Over S} (f : T' ⟶ T) (g : T'' ⟶ T') :
    CommSq ((pullbackComp f g).hom.app (obj T)) ((pullback g).map (transition f))
      (transition (g ≫ f)) (transition g)
  /-- A transition along an étale morphism is invertible. -/
  transition_isIso {T T' : Over S} (f : T' ⟶ T) (hf : Etale f.left) :
    IsIso (transition f)

namespace Object

/-- The fields of a compatible small-étale system express identity, composition, and étale
invertibility of its transition maps. -/
theorem spec (F : Object S) :
    (∀ T : Over S, F.transition (𝟙 T) = (pullbackId T).hom.app (F.obj T)) ∧
      (∀ {T T' T'' : Over S} (f : T' ⟶ T) (g : T'' ⟶ T'),
        CommSq ((pullbackComp f g).hom.app (F.obj T))
          ((pullback g).map (F.transition f)) (F.transition (g ≫ f)) (F.transition g)) ∧
      (∀ {T T' : Over S} (f : T' ⟶ T) (hf : Etale f.left), IsIso (F.transition f)) := sorry

end Object

/-- A morphism of compatible small-étale systems is a componentwise sheaf morphism commuting
with every transition map. -/
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

end Hom

/-- The category of compatible systems, bundled without installing a global category instance on
the explicit object structure. -/
noncomputable def category (S : Scheme.{u}) : Cat :=
  { α := Object S
    str :=
      { Hom := Hom
        id := Hom.id
        comp := Hom.comp
        id_comp := sorry
        comp_id := sorry
        assoc := sorry } }

/-- The map adjoint to the canonical transition from a big étale sheaf, expressed through direct
small-site base change. -/
noncomputable def fromSheafTransitionAdjoint
    (𝒢 : Sheaf (S.overGrothendieckTopology @Etale) (Type (u + 1)))
    {T T' : Over S} (f : T' ⟶ T) :
    (SmallToBig.inverseImage T.hom).obj 𝒢 ⟶
      ((smallEtalePullback f.left).sheafPushforwardContinuous (Type (u + 1))
        T.left.smallEtaleTopology T'.left.smallEtaleTopology).obj
          ((SmallToBig.inverseImage T'.hom).obj 𝒢) :=
  ObjectProperty.homMk
    { app := fun U ↦
        𝒢.1.map
          (Over.homMk (pullback.fst U.unop.hom f.left) sorry :
            (SmallToBig.relocalizationFunctor T'.hom).obj
                ((smallEtalePullback f.left).obj U.unop) ⟶
              (SmallToBig.relocalizationFunctor T.hom).obj U.unop).op
      naturality := sorry }

/-- The canonical transition of the compatible system associated to a big étale sheaf. -/
noncomputable def fromSheafTransition
    (𝒢 : Sheaf (S.overGrothendieckTopology @Etale) (Type (u + 1)))
    {T T' : Over S} (f : T' ⟶ T) :
    (pullback f).obj ((SmallToBig.inverseImage T.hom).obj 𝒢) ⟶
      (SmallToBig.inverseImage T'.hom).obj 𝒢 :=
  ((smallEtalePullback f.left).sheafAdjunctionContinuous (Type (u + 1))
    T.left.smallEtaleTopology T'.left.smallEtaleTopology).homEquiv _ _ |>.symm
      (fromSheafTransitionAdjoint 𝒢 f)

namespace Object

/-- The compatible system of small-étale sheaves obtained by restricting a big étale sheaf. -/
noncomputable def ofSheaf
    (𝒢 : Sheaf (S.overGrothendieckTopology @Etale) (Type (u + 1))) : Object S where
  obj T := (SmallToBig.inverseImage T.hom).obj 𝒢
  transition f := fromSheafTransition 𝒢 f
  transition_id _ := sorry
  transition_comp _ _ := sorry
  transition_isIso _ _ := sorry

end Object

/-- A morphism of big étale sheaves induces the componentwise compatible morphism between their
small-étale systems. -/
noncomputable def fromSheafMap
    {𝒢 ℋ : Sheaf (S.overGrothendieckTopology @Etale) (Type (u + 1))} (η : 𝒢 ⟶ ℋ) :
    Hom (Object.ofSheaf 𝒢) (Object.ofSheaf ℋ) where
  app T := (SmallToBig.inverseImage T.hom).map η
  naturality _ := sorry

/-- Restriction of big étale sheaves to their compatible systems on all small étale sites. -/
noncomputable def fromSheaf (S : Scheme.{u}) :
    Sheaf (S.overGrothendieckTopology @Etale) (Type (u + 1)) ⥤ category S where
  obj := Object.ofSheaf
  map := fromSheafMap
  map_id := sorry
  map_comp := sorry

/-- Restriction from the big étale site to compatible sheaves on all small étale sites is an
equivalence of categories. -/
theorem fromSheaf_isEquivalence (S : Scheme.{u}) :
    Functor.IsEquivalence (fromSheaf S) := sorry

end AlgebraicGeometry.Scheme.Etale.SmallGlueing
