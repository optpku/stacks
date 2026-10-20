module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.InverseSystem.Preorder
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-!
# Sheaf systems on inverse systems of schemes

This module packages compatible set-valued sheaves on the small etale sites of a
preorder-indexed inverse system of schemes.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe uI u uI' u'

namespace AlgebraicGeometry.Scheme.Etale.SheafSystem

variable {I : Type uI} [Preorder I]

/-- Pullback of set-valued sheaves along a transition of an inverse system of schemes. -/
noncomputable abbrev pullback (D : PreorderInverseSystem I Scheme.{u})
    {i j : I} (hij : i ≤ j) :
    Sheaf (D.obj (Opposite.op i)).smallEtaleTopology (Type (u + 1)) ⥤
      Sheaf (D.obj (Opposite.op j)).smallEtaleTopology (Type (u + 1)) :=
  (Scheme.smallEtalePullback (D.transitionMap hij)).sheafPullback (Type (u + 1))
    (D.obj (Opposite.op i)).smallEtaleTopology
    (D.obj (Opposite.op j)).smallEtaleTopology

/-- `pullback` is the canonical sheaf pullback along small-etale base change. -/
theorem pullback_def (D : PreorderInverseSystem I Scheme.{u})
    {i j : I} (hij : i ≤ j) :
    pullback D hij =
      (Scheme.smallEtalePullback (D.transitionMap hij)).sheafPullback (Type (u + 1))
        (D.obj (Opposite.op i)).smallEtaleTopology
        (D.obj (Opposite.op j)).smallEtaleTopology := sorry

/-- Successive pullbacks along inverse-system transitions are canonically isomorphic to
pullback along the composite transition. -/
noncomputable def pullbackCompIso (D : PreorderInverseSystem I Scheme.{u})
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    pullback D hij ⋙ pullback D hjk ≅ pullback D (le_trans hij hjk) :=
  let mapEq : D.transitionMap (le_trans hij hjk) =
      D.transitionMap hjk ≫ D.transitionMap hij :=
    D.map_comp (homOfLE hjk).op (homOfLE hij).op
  let siteIso :
      Scheme.smallEtalePullback (D.transitionMap hij) ⋙
          Scheme.smallEtalePullback (D.transitionMap hjk) ≅
        Scheme.smallEtalePullback (D.transitionMap (le_trans hij hjk)) :=
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      (D.transitionMap hjk) (D.transitionMap hij)).symm ≪≫
        eqToIso (congrArg Scheme.smallEtalePullback mapEq.symm)
  Adjunction.leftAdjointCompIso
    ((Scheme.smallEtalePullback (D.transitionMap hij)).sheafAdjunctionContinuous
      (Type (u + 1)) (D.obj (Opposite.op i)).smallEtaleTopology
        (D.obj (Opposite.op j)).smallEtaleTopology)
    ((Scheme.smallEtalePullback (D.transitionMap hjk)).sheafAdjunctionContinuous
      (Type (u + 1)) (D.obj (Opposite.op j)).smallEtaleTopology
        (D.obj (Opposite.op k)).smallEtaleTopology)
    ((Scheme.smallEtalePullback (D.transitionMap (le_trans hij hjk))).sheafAdjunctionContinuous
      (Type (u + 1)) (D.obj (Opposite.op i)).smallEtaleTopology
        (D.obj (Opposite.op k)).smallEtaleTopology)
    (Functor.sheafPushforwardContinuousComp' siteIso
      (Type (u + 1)) (D.obj (Opposite.op i)).smallEtaleTopology
        (D.obj (Opposite.op j)).smallEtaleTopology
          (D.obj (Opposite.op k)).smallEtaleTopology)

/-- The component of `pullbackCompIso` is natural in the sheaf being pulled back. -/
theorem pullbackCompIso_hom_naturality (D : PreorderInverseSystem I Scheme.{u})
    {i j k : I} (hij : i ≤ j) (hjk : j ≤ k)
    {F G : Sheaf (D.obj (Opposite.op i)).smallEtaleTopology (Type (u + 1))}
    (f : F ⟶ G) :
    (pullback D hij ⋙ pullback D hjk).map f ≫
        (pullbackCompIso D hij hjk).hom.app G =
      (pullbackCompIso D hij hjk).hom.app F ≫
        (pullback D (le_trans hij hjk)).map f := sorry

end AlgebraicGeometry.Scheme.Etale.SheafSystem

namespace AlgebraicGeometry.Scheme.Etale

/-- A compatible system of sheaves on the small etale sites of a preorder-indexed inverse
system of schemes. -/
structure SheafSystem
    {I : Type uI'} [Preorder I]
    (D : PreorderInverseSystem I Scheme.{u'}) where
  /-- The sheaf on the small etale site of the scheme at `i`. -/
  obj (i : I) :
    Sheaf (D.obj (Opposite.op i)).smallEtaleTopology (Type (u' + 1))
  /-- The transition from the pullback of the sheaf at `i` to the sheaf at `j`. -/
  transition {i j : I} (hij : i ≤ j) :
    (AlgebraicGeometry.Scheme.Etale.SheafSystem.pullback D hij).obj (obj i) ⟶ obj j
  /-- Transition morphisms satisfy the three-index pullback cocycle law. -/
  transition_comp {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    (AlgebraicGeometry.Scheme.Etale.SheafSystem.pullbackCompIso D hij hjk).hom.app (obj i) ≫
        transition (le_trans hij hjk) =
      (AlgebraicGeometry.Scheme.Etale.SheafSystem.pullback D hjk).map (transition hij) ≫
        transition hjk

end AlgebraicGeometry.Scheme.Etale

namespace AlgebraicGeometry.Scheme.Etale.SheafSystem

variable {I : Type uI} [Preorder I]
variable {D : PreorderInverseSystem I Scheme.{u}}

/-- Construct a sheaf system from its stage sheaves, transition morphisms, and cocycle law. -/
def of
    (obj : (i : I) →
      Sheaf (D.obj (Opposite.op i)).smallEtaleTopology (Type (u + 1)))
    (transition : ∀ {i j : I} (hij : i ≤ j),
      (pullback D hij).obj (obj i) ⟶ obj j)
    (transition_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
      (pullbackCompIso D hij hjk).hom.app (obj i) ≫
          transition (le_trans hij hjk) =
        (pullback D hjk).map (transition hij) ≫ transition hjk) :
    SheafSystem D where
  obj := obj
  transition := transition
  transition_comp := transition_comp

/-- The stage sheaf of `SheafSystem.of` is the supplied stage sheaf. -/
theorem of_obj
    (obj : (i : I) →
      Sheaf (D.obj (Opposite.op i)).smallEtaleTopology (Type (u + 1)))
    (transition : ∀ {i j : I} (hij : i ≤ j),
      (pullback D hij).obj (obj i) ⟶ obj j)
    (transition_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
      (pullbackCompIso D hij hjk).hom.app (obj i) ≫
          transition (le_trans hij hjk) =
        (pullback D hjk).map (transition hij) ≫ transition hjk)
    (i : I) :
    (of obj transition transition_comp).obj i = obj i := sorry

/-- The transition of `SheafSystem.of` is the supplied transition morphism. -/
theorem of_transition
    (obj : (i : I) →
      Sheaf (D.obj (Opposite.op i)).smallEtaleTopology (Type (u + 1)))
    (transition : ∀ {i j : I} (hij : i ≤ j),
      (pullback D hij).obj (obj i) ⟶ obj j)
    (transition_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
      (pullbackCompIso D hij hjk).hom.app (obj i) ≫
          transition (le_trans hij hjk) =
        (pullback D hjk).map (transition hij) ≫ transition hjk)
    {i j : I} (hij : i ≤ j) :
    (of obj transition transition_comp).transition hij = transition hij := sorry

/-- The transition maps of a sheaf system satisfy the three-index pullback cocycle law. -/
theorem spec (F : SheafSystem D) {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    (pullbackCompIso D hij hjk).hom.app (F.obj i) ≫
        F.transition (le_trans hij hjk) =
      (pullback D hjk).map (F.transition hij) ≫ F.transition hjk := sorry

end AlgebraicGeometry.Scheme.Etale.SheafSystem
