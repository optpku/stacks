/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import ReasLib.Topology.Opens.Inclusion

/-!
# Modules on open subspaces

This module provides the canonical restriction functor for sheaves of modules along an open
subspace inclusion and its comparison with the open-embedding model. The explicit extension-by-zero
construction and its adjunction are owned by
`SheafOfModules.OpenSubset.ExtensionByZero`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules.OpenSubset.Restriction

variable {X : TopCat.{u}} (U : Opens X) (𝒪 : TopCat.Sheaf RingCat.{u} X)

/-- For an open subset `U ⊆ X`, the restriction functor on sheaves of `𝒪`-modules to `U` is the
inverse-image functor along the open
inclusion `j : U ↪ X`, modeled by the pullback of module sheaves along the unit
`𝒪 ⟶ j_* j^{-1} 𝒪`. -/
noncomputable abbrev functor :
    SheafOfModules 𝒪 ⥤
      SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj 𝒪) :=
  SheafOfModules.pullback
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪)

/-- The concrete restriction functor on module sheaves obtained from the open-embedding model.

Unlike `functor U 𝒪`, this uses the pullback comparison induced directly by the open embedding;
`openEmbeddingIso U 𝒪` identifies the two restriction models. -/
noncomputable abbrev openEmbeddingFunctor :
    SheafOfModules 𝒪 ⥤
      SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj 𝒪) :=
  SheafOfModules.pushforward.{u} (F := U.isOpenEmbedding.functor)
    (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app 𝒪).hom)

/-- The restriction owner is the pullback side of the canonical pullback/pushforward adjunction
for the open inclusion
`U ↪ X`. -/
noncomputable def adjunction :
    functor U 𝒪 ⊣
      SheafOfModules.pushforward
        ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪) :=
  SheafOfModules.pullbackPushforwardAdjunction
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪)

-- Proof sketch: besides the extension-by-zero adjunction sought below, restriction already comes
-- with its canonical left-adjoint structure from the pullback/direct-image formalism.
/-- The module-valued restriction owner is also a left adjoint to the direct-image functor attached
to the open inclusion. -/
instance functor_isLeftAdjoint :
    (functor U 𝒪).IsLeftAdjoint := sorry

/-- The inverse component
of `TopCat.Sheaf.pullbackIso` carries the sheafified presheaf pullback-unit section back to the
genuine sheaf pullback-unit section. -/
private theorem pullbackIso_inv_toSheafify_unit_section_eq
    {Y T : TopCat.{u}} (f : Y ⟶ T) (𝒢 : T.Sheaf RingCat.{u}) (V : Opens T)
    (s : 𝒢.1.obj (Opposite.op V)) :
    (((TopCat.Sheaf.pullbackIso RingCat.{u} f).inv.app 𝒢).1.app
        (Opposite.op ((Opens.map f).obj V)))
      (((CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.forget RingCat.{u} T ⋙ TopCat.Presheaf.pullback RingCat.{u} f).obj 𝒢)).app
          (Opposite.op ((Opens.map f).obj V)))
        ((((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒢.1).app
            (Opposite.op V)) s)) =
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒢).1.app
          (Opposite.op V)) s) := sorry

/-- On presheaf sections,
the open-map pullback comparison sends the presheaf pullback adjunction unit to restriction along
the opens-adjunction counit. -/
private abbrev open_embedding_presheaf_unit_app
    (W : Opens X) :
    𝒪.obj.obj (Opposite.op W) ⟶
      ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪.obj).obj
        (Opposite.op ((Opens.map U.inclusion').obj W)) :=
  ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪.obj).app
    (Opposite.op W)

/-- The presheaf pullback
adjunction unit evaluated on the image open `U ∩ W`. -/
private abbrev open_embedding_presheaf_unit_functor_app
    (V : Opens ((Opens.toTopCat X).obj U)) :
    (U.isOpenEmbedding.functor.op ⋙ 𝒪.obj).obj (Opposite.op V) ⟶
      ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪.obj).obj
        (Opposite.op ((Opens.map U.inclusion').obj (U.isOpenEmbedding.functor.obj V))) :=
  ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪.obj).app
    (Opposite.op (U.isOpenEmbedding.functor.obj V))

/-- On presheaf sections,
the open-map pullback comparison sends the presheaf pullback adjunction unit to restriction along
the opens-adjunction counit. -/
private theorem open_embedding_presheaf_counit_app
    (W : Opens X) (s : 𝒪.obj.obj (Opposite.op W)) :
    ((U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪.obj).hom.app
        (Opposite.op ((Opens.map U.inclusion').obj W)))
      ((open_embedding_presheaf_unit_app (U := U) (𝒪 := 𝒪) W) s) =
      (𝒪.obj.map (U.isOpenEmbedding.isOpenMap.adjunction.counit.app W).op) s := sorry

/-- On presheaf sections,
the inverse open-map pullback comparison followed by restriction along the opens-adjunction unit is
the identity. -/
private theorem open_embedding_pullbackObjIso_hom_unit_app
    (V : Opens ((Opens.toTopCat X).obj U))
    (s : ((U.isOpenEmbedding.functor.op ⋙ 𝒪.obj).obj (Opposite.op V))) :
    ((U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪.obj).hom.app (Opposite.op V))
      ((((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪.obj).map
          (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
        ((open_embedding_presheaf_unit_functor_app (U := U) (𝒪 := 𝒪) V) s)) =
      ((U.isOpenEmbedding.functor.op ⋙ 𝒪.obj).map
          (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
        (((U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪.obj).hom.app
            (Opposite.op ((Opens.map U.inclusion').obj (U.isOpenEmbedding.functor.obj V))))
          ((open_embedding_presheaf_unit_functor_app (U := U) (𝒪 := 𝒪) V) s)) := sorry

/-- On presheaf sections,
the inverse open-map pullback comparison followed by restriction along the opens-adjunction unit is
the identity. -/
private theorem open_embedding_presheaf_triangle_app
    (V : Opens ((Opens.toTopCat X).obj U))
    (s : (U.isOpenEmbedding.functor.op ⋙ 𝒪.obj).obj (Opposite.op V)) :
    (((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪.obj).map
        (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
      ((open_embedding_presheaf_unit_functor_app (U := U) (𝒪 := 𝒪) V) s) =
      (((U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪.obj).inv.app (Opposite.op V)) s) := sorry

/-- After rewriting the
sheaf pullback unit section through `TopCat.Sheaf.pullbackIso`, the remaining `sheafPullbackIso`
component evaluates to the open-map pullback comparison on the presheaf unit section. -/
private theorem open_embedding_pullbackIso_inv_hom_section_cancel
    (W : Opens ((Opens.toTopCat X).obj U))
    (t : (((CategoryTheory.sheafify
      (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
      ((TopCat.Sheaf.forget RingCat.{u} X ⋙
        TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪))).obj
      (Opposite.op W))) :
    (RingCat.Hom.hom
        (((TopCat.Sheaf.pullbackIso RingCat.{u} U.inclusion').hom.app 𝒪).1.app
          (Opposite.op W)))
      ((((TopCat.Sheaf.pullbackIso RingCat.{u} U.inclusion').inv.app 𝒪).1.app
          (Opposite.op W)) t) = t := sorry

/-- After rewriting the
sheaf pullback unit section through `TopCat.Sheaf.pullbackIso`, the remaining `sheafPullbackIso`
component evaluates to the open-map pullback comparison on the presheaf unit section. -/
private theorem open_embedding_sheaf_pullback_tail_on_toSheafify_section
    (W : Opens ((Opens.toTopCat X).obj U))
    (t : ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪.obj).obj (Opposite.op W)) :
    (RingCat.Hom.hom
        ((((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app 𝒪).hom).hom.app
          (Opposite.op W)))
      (((((TopCat.Sheaf.pullbackIso RingCat.{u} U.inclusion').inv.app 𝒪).1.app
          (Opposite.op W))
        (((CategoryTheory.toSheafify
            (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
            ((TopCat.Sheaf.forget RingCat.{u} X ⋙
              TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪)).app
            (Opposite.op W))
          t))) =
      ((U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪.obj).hom.app (Opposite.op W)) t := sorry

/-- After rewriting the
sheaf pullback unit section through `TopCat.Sheaf.pullbackIso`, the remaining `sheafPullbackIso`
component evaluates to the open-map pullback comparison on the presheaf unit section. -/
private theorem open_embedding_sheaf_pullback_counit_section_adapter
    (W : Opens X) (s : 𝒪.obj.obj (Opposite.op W)) :
    (RingCat.Hom.hom
        ((((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app 𝒪).hom).hom.app
          (Opposite.op ((Opens.map U.inclusion').obj W))))
      (((((TopCat.Sheaf.pullbackIso RingCat.{u} U.inclusion').inv.app 𝒪).1.app
          (Opposite.op ((Opens.map U.inclusion').obj W)))
      (((CategoryTheory.toSheafify
            (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
            ((TopCat.Sheaf.forget RingCat.{u} X ⋙
              TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪)).app
            (Opposite.op ((Opens.map U.inclusion').obj W)))
          ((open_embedding_presheaf_unit_app (U := U) (𝒪 := 𝒪) W) s)))) =
      ((U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪.obj).hom.app
        (Opposite.op ((Opens.map U.inclusion').obj W)))
        ((open_embedding_presheaf_unit_app (U := U) (𝒪 := 𝒪) W) s) := sorry

/-- The counit comparison
needed to transport the open-subset adjunction to sheaves of `𝒪`-modules. -/
lemma openEmbeddingCounitEq :
    Functor.whiskerRight (NatTrans.op U.isOpenEmbedding.isOpenMap.adjunction.counit) 𝒪.obj =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪).hom ≫
        (Opens.map U.inclusion').op.whiskerLeft
          (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app 𝒪).hom).hom := sorry

/-- Transporting the full
unit-side composite across `U.isOpenEmbedding.sheafPullbackIso` identifies it with the presheaf
pullback comparison applied to the presheaf triangle input. -/
private theorem open_embedding_unit_section_transport_adapter
    (V : Opens ((Opens.toTopCat X).obj U))
    (s : (U.isOpenEmbedding.functor.op ⋙ 𝒪.obj).obj (Opposite.op V)) :
    (RingCat.Hom.hom
        ((((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app 𝒪).hom).hom.app
          (Opposite.op V)))
      ((RingCat.Hom.hom
          (((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj 𝒪).obj.map
            (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op))
        ((RingCat.Hom.hom
            (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪).hom.app
              (Opposite.op (U.isOpenEmbedding.functor.obj V))))
          s)) =
      ((U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒪.obj).hom.app (Opposite.op V))
        ((((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj 𝒪.obj).map
            (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
          ((open_embedding_presheaf_unit_functor_app (U := U) (𝒪 := 𝒪) V) s)) := sorry

/-- After transporting the
full unit-side composite across `U.isOpenEmbedding.sheafPullbackIso`, the remaining presheaf
composite collapses by the open-embedding triangle identity. -/
private theorem open_embedding_unit_section_transport_normalized
    (V : Opens ((Opens.toTopCat X).obj U))
    (s : (U.isOpenEmbedding.functor.op ⋙ 𝒪.obj).obj (Opposite.op V)) :
    (RingCat.Hom.hom
        ((((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app 𝒪).hom).hom.app
          (Opposite.op V)))
      ((RingCat.Hom.hom
          (((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj 𝒪).obj.map
            (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op))
        ((RingCat.Hom.hom
            (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪).hom.app
              (Opposite.op (U.isOpenEmbedding.functor.obj V))))
          s)) = s := sorry

/-- The unit comparison
needed to transport the open-subset adjunction to sheaves of `𝒪`-modules. -/
lemma openEmbeddingUnitEq :
    (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app 𝒪).hom).hom ≫
        U.isOpenEmbedding.functor.op.whiskerLeft
          ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪).hom ≫
        Functor.whiskerRight (NatTrans.op U.isOpenEmbedding.isOpenMap.adjunction.unit)
          ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj 𝒪).obj =
      𝟙 ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj 𝒪).obj := sorry

/-- The open-embedding
restriction owner is also a left adjoint to the module direct image along `U ↪ X`. -/
noncomputable abbrev openEmbeddingAdjunction :
    openEmbeddingFunctor U 𝒪 ⊣
      SheafOfModules.pushforward
        ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪) :=
  -- The open-embedding pushforward owner becomes a left adjoint once the two comparison
  -- identities above identify its unit and counit with the open-subset adjunction data.
  SheafOfModules.pushforwardPushforwardAdj
    (adj := U.isOpenEmbedding.isOpenMap.adjunction)
    (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app 𝒪).hom)
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app 𝒪)
    (openEmbeddingCounitEq U 𝒪)
    (openEmbeddingUnitEq U 𝒪)

/-- The module direct image in the concrete open-embedding model is a right adjoint. -/
instance openEmbeddingPushforward_isRightAdjoint :
    (SheafOfModules.pushforward.{u} (F := U.isOpenEmbedding.functor)
      (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app 𝒪).hom)).IsRightAdjoint := sorry

/-- The concrete
open-embedding restriction owner agrees with the pullback-based public API. -/
noncomputable abbrev openEmbeddingIso :
    openEmbeddingFunctor U 𝒪 ≅ functor U 𝒪 :=
  -- The two functors are the unique left adjoints to the same module direct-image functor.
  Adjunction.leftAdjointUniq
    (openEmbeddingAdjunction U 𝒪)
    (adjunction U 𝒪)

-- Proof sketch: this is the module-valued analogue of the open-immersion restriction functor for
-- sheaves of sets and algebraic structures. One proves that for an open inclusion `j : U ↪ X`,
-- restriction of `𝒪`-modules has a left adjoint given by extension by zero, hence the displayed
-- restriction functor is a right adjoint.
/-- Restriction of sheaves of `𝒪`-modules to an open subset is a right adjoint. -/
instance functor_isRightAdjoint :
    (functor U 𝒪).IsRightAdjoint := sorry

end SheafOfModules.OpenSubset.Restriction
