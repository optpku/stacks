/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Hypercohomology.InverseSystem
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {I : Type u} [Preorder I]
variable (D : OrderDual I ⥤ Scheme.{u})
variable [∀ i : I, HasSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ i : I, HasWeakSheafify (D.obj (OrderDual.toDual i)).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ {S T : Scheme.{u}} (f : T ⟶ S)
    (G : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}),
    (smallEtalePullback f).op.HasLeftKanExtension G]
variable [∀ {S T : Scheme.{u}} (f : T ⟶ S),
    ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
      S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]
variable {S : Scheme.{u}}
variable [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
variable (σ : D ⟶ (const (OrderDual I)).obj S)
variable (K : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) ℤ)

/-- The structure morphism from a stage of an inverse system over `S` to `S`. -/
abbrev structureMap (i : I) : D.obj (OrderDual.toDual i) ⟶ S :=
  σ.app (OrderDual.toDual i)

/-- Structure maps of an inverse system over `S` compose with its transition maps. -/
theorem structureMap_comp {i j : I} (hij : i ≤ j) :
    structureMap D σ j =
      OrderDualInverseSystem.transitionMap D hij ≫ structureMap D σ i := sorry

/-- Inverse images of a complex along composable scheme morphisms are canonically isomorphic. -/
def inverseImageComplexCompIso {S T U : Scheme.{u}} (f : U ⟶ T) (g : T ⟶ S)
    [HasWeakSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [HasWeakSheafify U.smallEtaleTopology AddCommGrpCat.{u}]
    (K : CochainComplex (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) ℤ) :
    inverseImageComplex f (inverseImageComplex g K) ≅ inverseImageComplex (f ≫ g) K :=
  let siteIso :
      smallEtalePullback g ⋙ smallEtalePullback f ≅ smallEtalePullback (f ≫ g) :=
    (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g).symm
  (NatIso.mapHomologicalComplex
      (Adjunction.leftAdjointCompIso
        ((smallEtalePullback g).sheafAdjunctionContinuous AddCommGrpCat
          S.smallEtaleTopology T.smallEtaleTopology)
        ((smallEtalePullback f).sheafAdjunctionContinuous AddCommGrpCat
          T.smallEtaleTopology U.smallEtaleTopology)
        ((smallEtalePullback (f ≫ g)).sheafAdjunctionContinuous AddCommGrpCat
          S.smallEtaleTopology U.smallEtaleTopology)
        (Functor.sheafPushforwardContinuousComp' siteIso AddCommGrpCat
          S.smallEtaleTopology T.smallEtaleTopology U.smallEtaleTopology))
      (ComplexShape.up ℤ)).app K

/-- The transition morphism between pullbacks of one complex along two stages. -/
def pullbackComplexSystemTransition {i j : I} (hij : i ≤ j) :
    (transitionPullbackComplex D hij).obj (inverseImageComplex (structureMap D σ i) K) ⟶
      inverseImageComplex (structureMap D σ j) K :=
  (inverseImageComplexCompIso (OrderDualInverseSystem.transitionMap D hij)
      (structureMap D σ i) K).hom ≫
    eqToHom (congrArg (fun f => inverseImageComplex f K) (structureMap_comp D σ hij).symm)

/-- The compatible system of pullbacks of a fixed complex along an inverse system over `S`. -/
def pullbackComplexSystem : AbelianSheafComplexSystem D :=
  AbelianSheafComplexSystem.of
    (fun i => inverseImageComplex (structureMap D σ i) K)
    (fun {i j} hij => pullbackComplexSystemTransition D σ K hij)
    (fun {_ _ _} _ _ => sorry)

/-- The stage object of the pullback complex system is the corresponding inverse image. -/
theorem pullbackComplexSystem_obj (i : I) :
    (pullbackComplexSystem D σ K).obj i = inverseImageComplex (structureMap D σ i) K := sorry

variable [Nonempty I]
variable [IsDirected I (· ≤ ·)]
variable (c : Cone D)
variable [HasSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u}]

/-- The morphism from the limiting cone point to the base scheme induced by `σ`. -/
def limitStructureMap : c.pt ⟶ S :=
  c.π.app (OrderDual.toDual (Classical.choice ‹Nonempty I›)) ≫
    structureMap D σ (Classical.choice ‹Nonempty I›)

/-- Every cone projection followed by its structure map equals `limitStructureMap`. -/
theorem limitStructureMap_eq (i : I) :
    c.π.app (OrderDual.toDual i) ≫ structureMap D σ i = limitStructureMap D σ c := sorry

/-- Inverse images along a cone projection and the associated composite are canonically isomorphic. -/
def conePullbackInverseImageIso (i : I) :
    (AbelianSheafComplexSystem.conePullbackComplex (D := D) c i).obj
        (inverseImageComplex (structureMap D σ i) K) ≅
      inverseImageComplex (c.π.app (OrderDual.toDual i) ≫ structureMap D σ i) K :=
  inverseImageComplexCompIso (c.π.app (OrderDual.toDual i)) (structureMap D σ i) K

/-- The colimit of the pulled-back stage complexes is the pullback from the limiting cone point. -/
def colimitInverseImage_pullback_iso
    [HasColimit
      (AbelianSheafComplexSystem.inverseImageComplexDiagram (D := D) c
        (pullbackComplexSystem D σ K))] :
    AbelianSheafComplexSystem.colimitInverseImageComplex (D := D) c
        (pullbackComplexSystem D σ K) ≅
      inverseImageComplex (limitStructureMap D σ c) K :=
  let i0 : I := Classical.choice ‹Nonempty I›
  { hom :=
      colimit.desc
        (AbelianSheafComplexSystem.inverseImageComplexDiagram (D := D) c
          (pullbackComplexSystem D σ K))
        { pt := inverseImageComplex (limitStructureMap D σ c) K
          ι :=
            { app := fun i =>
                eqToHom (congrArg
                    (fun G =>
                      (AbelianSheafComplexSystem.conePullbackComplex (D := D) c i).obj G)
                    (pullbackComplexSystem_obj D σ K i)) ≫
                  (conePullbackInverseImageIso D σ K c i).hom ≫
                    eqToHom (congrArg (fun f => inverseImageComplex f K)
                      (limitStructureMap_eq D σ c i))
              naturality := sorry } }
    inv :=
      eqToHom (congrArg (fun f => inverseImageComplex f K)
          (limitStructureMap_eq D σ c i0).symm) ≫
        (conePullbackInverseImageIso D σ K c i0).inv ≫
          eqToHom (congrArg
              (fun G =>
                (AbelianSheafComplexSystem.conePullbackComplex (D := D) c i0).obj G)
              (pullbackComplexSystem_obj D σ K i0).symm) ≫
            AbelianSheafComplexSystem.colimitInverseImageComplex_ι (D := D) c
              (pullbackComplexSystem D σ K) i0
    hom_inv_id := sorry
    inv_hom_id := sorry }

variable [HasExt.{u} (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u}
    (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u})]
variable [Functor.HasRightDerivedFunctor
    (Functor.RightDerived.Cochain.toDerived
      (siteAbelianSectionsFunctor c.pt.smallEtaleTopology (globalEtale c.pt)))
    (HomologicalComplex.quasiIso
      (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))]
variable [∀ i : I, IsGrothendieckAbelian.{u}
    (Sheaf (((const (OrderDual I)).obj c.pt).obj (OrderDual.toDual i)).smallEtaleTopology
      AddCommGrpCat.{u})]
variable [∀ i : I,
    Functor.HasRightDerivedFunctor
      (Functor.RightDerived.Cochain.toDerived
        (siteAbelianSectionsFunctor
          (((const (OrderDual I)).obj c.pt).obj (OrderDual.toDual i)).smallEtaleTopology
          (globalEtale (((const (OrderDual I)).obj c.pt).obj (OrderDual.toDual i)))))
      (HomologicalComplex.quasiIso
        (Sheaf (((const (OrderDual I)).obj c.pt).obj (OrderDual.toDual i)).smallEtaleTopology
          AddCommGrpCat.{u})
        (ComplexShape.up ℤ))]
variable (a p : ℤ)
variable [HasColimit (hypercohomologyDiagram D (pullbackComplexSystem D σ K) p)]
variable [HasColimit
    (AbelianSheafComplexSystem.inverseImageComplexDiagram (D := D) c
      (pullbackComplexSystem D σ K))]

/-- The comparison from stage hypercohomology to hypercohomology on the limiting pullback. -/
def baseChangeComparison :
    colimit (hypercohomologyDiagram D (pullbackComplexSystem D σ K) p) ⟶
      etaleHypercohomology c.pt (inverseImageComplex (limitStructureMap D σ c) K) p :=
  complexComparison D (pullbackComplexSystem D σ K) c p ≫
    etaleHypercohomology.map (colimitInverseImage_pullback_iso D σ K c).hom p

/-- The base-change comparison is the compatible-system comparison followed by transport. -/
theorem baseChangeComparison_eq :
    baseChangeComparison D σ K c p =
      complexComparison D (pullbackComplexSystem D σ K) c p ≫
        etaleHypercohomology.map (colimitInverseImage_pullback_iso D σ K c).hom p := sorry

/-- Étale hypercohomology commutes with directed affine-transition limits of qcqs schemes for a
bounded-below complex pulled back from the base. -/
theorem etaleHypercohomology_colimit_baseChange
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap D hij)]
    [∀ i : I, CompactSpace (D.obj (OrderDual.toDual i))]
    [∀ i : I, QuasiSeparatedSpace (D.obj (OrderDual.toDual i))]
    (hc : IsLimit c) (hK : K.IsStrictlyGE a) :
    IsIso (baseChangeComparison D σ K c p) := sorry

end AlgebraicGeometry.Scheme.Etale

end
