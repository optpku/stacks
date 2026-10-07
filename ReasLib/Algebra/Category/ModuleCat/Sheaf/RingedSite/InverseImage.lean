module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous.Restrict
public import Mathlib.Algebra.Homology.Additive
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inverse image of modules on ringed sites

This file owns the change-of-rings data common to inverse-image constructions for module sheaves.
It is independent of any particular complex, such as a de Rham or cotangent complex.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.InverseImage

/-- The inverse-image functor on commutative ring sheaves along a continuous functor of sites. -/
abbrev ringPullback
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    [HasWeakSheafify K CommRingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P] :
    Sheaf J CommRingCat.{max u v} ⥤ Sheaf K CommRingCat.{max u v} :=
  F.sheafPullback CommRingCat J K

/-- The inverse image of the underlying ring sheaf, formed directly in `RingCat`. -/
abbrev underlyingRingPullback
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
    [HasWeakSheafify K RingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ RingCat.{max u v}, F.op.HasLeftKanExtension P]
    (O : Sheaf J CommRingCat.{max u v}) : Sheaf K RingCat.{max u v} :=
  (F.sheafPullback RingCat.{max u v} J K).obj (ringSheaf J O)

/-- The unit of commutative-ring sheaf inverse image along a continuous functor of sites. -/
abbrev ringUnit
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    [HasWeakSheafify K CommRingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
    (O : Sheaf J CommRingCat.{max u v}) :
    O ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u v} J K).obj
      ((ringPullback (J := J) (K := K) F).obj O) :=
  (F.sheafAdjunctionContinuous CommRingCat.{max u v} J K).unit.app O

/-- The unit of inverse image applied directly to the underlying ring sheaf. -/
abbrev underlyingRingUnit
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
    [HasWeakSheafify K RingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ RingCat.{max u v}, F.op.HasLeftKanExtension P]
    (O : Sheaf J CommRingCat.{max u v}) :
    ringSheaf J O ⟶
      (F.sheafPushforwardContinuous RingCat.{max u v} J K).obj
        (underlyingRingPullback (J := J) (K := K) F O) :=
  (F.sheafAdjunctionContinuous RingCat.{max u v} J K).unit.app (ringSheaf J O)

/-- Transpose an adjoint-side morphism of commutative ring sheaves to the inverse-image side. -/
noncomputable def adjointMap
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    [HasWeakSheafify K CommRingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
    {O : Sheaf J CommRingCat.{max u v}} {O' : Sheaf K CommRingCat.{max u v}}
    (g : O ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u v} J K).obj O') :
    (ringPullback (J := J) (K := K) F).obj O ⟶ O' :=
  ((F.sheafAdjunctionContinuous CommRingCat.{max u v} J K).homEquiv _ _).symm g

/-- Forget commutativity in an adjoint-side ring-sheaf morphism, obtaining the structure map used
for inverse image of module sheaves. -/
abbrev underlyingMap
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
    [K.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
    {O : Sheaf J CommRingCat.{max u v}} {O' : Sheaf K CommRingCat.{max u v}}
    (g : O ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u v} J K).obj O') :
    ringSheaf J O ⟶
      (F.sheafPushforwardContinuous RingCat.{max u v} J K).obj (ringSheaf K O') :=
  (sheafCompose J (forget₂ CommRingCat RingCat.{max u v})).map g

/-- Naturality of the inverse-image unit gives the canonical adjoint-side square for a
commutative-ring sheaf morphism. -/
theorem ringUnitSquare
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    [HasWeakSheafify K CommRingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
    {O O' : Sheaf J CommRingCat.{max u v}} (f : O ⟶ O') :
    CommSq (ringUnit (J := J) (K := K) F O) f
      ((F.sheafPushforwardContinuous CommRingCat.{max u v} J K).map
        ((ringPullback (J := J) (K := K) F).map f))
      (ringUnit (J := J) (K := K) F O') := sorry

/-- Transposing the inverse-image unit gives the identity of the pulled-back ring sheaf. -/
@[simp]
theorem adjointMap_ringUnit
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    [HasWeakSheafify K CommRingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
    (O : Sheaf J CommRingCat.{max u v}) :
    adjointMap (J := J) (K := K) F (ringUnit (J := J) (K := K) F O) = 𝟙 _ := sorry

/-- The transpose of the inverse-image unit is canonically invertible. -/
instance adjointMap_ringUnit_isIso
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    [HasWeakSheafify K CommRingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
    (O : Sheaf J CommRingCat.{max u v}) :
    IsIso (adjointMap (J := J) (K := K) F
      (ringUnit (J := J) (K := K) F O)) := sorry

/-- The structure map defining inverse image of modules over the underlying ring sheaf. -/
abbrev structureMap
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
    [K.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
    [HasWeakSheafify K CommRingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
    (O : Sheaf J CommRingCat.{max u v}) :
    ringSheaf J O ⟶
      (F.sheafPushforwardContinuous RingCat.{max u v} J K).obj
        (ringSheaf K ((ringPullback (J := J) (K := K) F).obj O)) :=
  (sheafCompose J (forget₂ CommRingCat RingCat.{max u v})).map
    (ringUnit (J := J) (K := K) F O)

/-- Inverse image of module sheaves along the structure map induced by a commutative ring
sheaf. -/
noncomputable abbrev modulePullback
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
    [K.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
    [HasWeakSheafify K CommRingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
    (O : Sheaf J CommRingCat.{max u v})
    [(SheafOfModules.pushforward (structureMap (J := J) (K := K) F O)).IsRightAdjoint] :
    ringedSiteModuleCategory J O ⥤
      ringedSiteModuleCategory K ((ringPullback (J := J) (K := K) F).obj O) :=
  SheafOfModules.pullback (structureMap (J := J) (K := K) F O)

/-- Inverse image of module sheaves formed directly from the unit on the underlying ring sheaf. -/
noncomputable abbrev underlyingModulePullback
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
    [HasWeakSheafify K RingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ RingCat.{max u v}, F.op.HasLeftKanExtension P]
    (O : Sheaf J CommRingCat.{max u v})
    [(SheafOfModules.pushforward
      (underlyingRingUnit (J := J) (K := K) F O)).IsRightAdjoint] :
    ringedSiteModuleCategory J O ⥤
      SheafOfModules (underlyingRingPullback (J := J) (K := K) F O) :=
  SheafOfModules.pullback (underlyingRingUnit (J := J) (K := K) F O)

/-- The canonical comparison between forgetting commutativity after pullback and pulling back the
underlying ring sheaf. -/
noncomputable def ringSheafPullbackIso
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
    [K.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
    [HasWeakSheafify K CommRingCat.{max u v}]
    [HasWeakSheafify K RingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ RingCat.{max u v}, F.op.HasLeftKanExtension P]
    [(forget₂ CommRingCat RingCat.{max u v}).PreservesLeftKanExtensions F.op]
    [K.PreservesSheafification (forget₂ CommRingCat RingCat.{max u v})]
    (O : Sheaf J CommRingCat.{max u v}) :
    ringSheaf K ((ringPullback (J := J) (K := K) F).obj O) ≅
      underlyingRingPullback (J := J) (K := K) F O :=
  (Functor.sheafPullback.compSheafComposeIso F
    (forget₂ CommRingCat RingCat.{max u v}) J K).app O

/-- The canonical comparison of pulled-back underlying ring sheaves intertwines the
commutative-ring structure map with the unit formed directly in `RingCat`. -/
@[reassoc]
theorem structureMap_comp_ringSheafPullbackIso_hom
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
    [K.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
    [HasWeakSheafify K CommRingCat.{max u v}]
    [HasWeakSheafify K RingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
    [∀ P : Cᵒᵖ ⥤ RingCat.{max u v}, F.op.HasLeftKanExtension P]
    [(forget₂ CommRingCat RingCat.{max u v}).PreservesLeftKanExtensions F.op]
    [K.PreservesSheafification (forget₂ CommRingCat RingCat.{max u v})]
    (O : Sheaf J CommRingCat.{max u v}) :
    structureMap (J := J) (K := K) F O ≫
        (F.sheafPushforwardContinuous RingCat.{max u v} J K).map
          (ringSheafPullbackIso (J := J) (K := K) F O).hom =
      underlyingRingUnit (J := J) (K := K) F O := sorry

/-- Inverse image of module sheaves preserves zero morphisms and hence acts degreewise on
homological complexes. -/
instance pullbackPreservesZeroMorphisms
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
    [K.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
    [HasWeakSheafify K CommRingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
    (O : Sheaf J CommRingCat.{max u v})
    [(SheafOfModules.pushforward (structureMap (J := J) (K := K) F O)).IsRightAdjoint] :
    (modulePullback (J := J) (K := K) F O).PreservesZeroMorphisms := sorry

/-- The direct inverse image presentation over the pulled-back underlying ring sheaf also
preserves zero morphisms. -/
instance underlyingPullbackPreservesZeroMorphisms
    {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
    [HasWeakSheafify K RingCat.{max u v}]
    [∀ P : Cᵒᵖ ⥤ RingCat.{max u v}, F.op.HasLeftKanExtension P]
    (O : Sheaf J CommRingCat.{max u v})
    [(SheafOfModules.pushforward
      (underlyingRingUnit (J := J) (K := K) F O)).IsRightAdjoint] :
    (underlyingModulePullback (J := J) (K := K) F O).PreservesZeroMorphisms := sorry

namespace Factorization

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (F : C ⥤ D) [F.IsContinuous J K]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
variable [K.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
variable [HasWeakSheafify K CommRingCat.{max u v}]
variable [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
variable {O : Sheaf J CommRingCat.{max u v}}
variable {O' : Sheaf K CommRingCat.{max u v}}

/-- The underlying ring-sheaf map of the adjoint-side coefficient morphism. -/
@[stacks 03D6 "underlying adjoint coefficient map"]
noncomputable abbrev underlyingAdjointMap
    (g : O ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u v} J K).obj O') :
    ringSheaf K ((ringPullback (J := J) (K := K) F).obj O) ⟶ ringSheaf K O' :=
  (sheafCompose K (forget₂ CommRingCat RingCat.{max u v})).map
    (adjointMap (J := J) (K := K) F g)

/-- The adjoint-side coefficient map factors through the inverse-image unit and its transpose. -/
theorem adjointMap_factorization
    (g : O ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u v} J K).obj O') :
    ringUnit (J := J) (K := K) F O ≫
        (F.sheafPushforwardContinuous CommRingCat.{max u v} J K).map
          (adjointMap (J := J) (K := K) F g) =
      g := sorry

/-- After forgetting commutativity, the full coefficient map factors through the inverse-image
unit followed by the underlying adjoint-side map. -/
theorem underlyingMap_factorization
    (g : O ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u v} J K).obj O') :
    structureMap (J := J) (K := K) F O ≫
        (F.sheafPushforwardContinuous RingCat.{max u v} J K).map
          (underlyingAdjointMap (J := J) (K := K) F g) =
      underlyingMap (J := J) (K := K) F g := sorry

/-- Pullback factored as inverse image followed by extension of scalars is left adjoint to the
full module pushforward. -/
@[stacks 03D6 "module pullback factorization adjunction"]
noncomputable def adjunction
    (g : O ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u v} J K).obj O')
    [(SheafOfModules.pushforward
      (structureMap (J := J) (K := K) F O)).IsRightAdjoint]
    [(SheafOfModules.restrictScalars
      (underlyingAdjointMap (J := J) (K := K) F g)).IsRightAdjoint] :
    modulePullback (J := J) (K := K) F O ⋙
        SheafOfModules.ChangeOfRings.extendScalars
          (underlyingAdjointMap (J := J) (K := K) F g) ⊣
      SheafOfModules.pushforward (underlyingMap (J := J) (K := K) F g) :=
  ((SheafOfModules.pullbackPushforwardAdjunction
      (structureMap (J := J) (K := K) F O)).comp
    (SheafOfModules.ChangeOfRings.extendRestrictAdjunction
      (underlyingAdjointMap (J := J) (K := K) F g))).ofNatIsoRight
        (SheafOfModules.restrictPushforwardIso
          (underlyingAdjointMap (J := J) (K := K) F g)
          (structureMap (J := J) (K := K) F O)
          (underlyingMap (J := J) (K := K) F g)
          (underlyingMap_factorization (J := J) (K := K) F g))

/-- Canonical factorization of module pullback into inverse image over `F⁻¹O` followed by
extension of scalars along the adjoint-side coefficient map. -/
@[stacks 03D6 "module pullback factorization"]
noncomputable def pullbackIso
    (g : O ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u v} J K).obj O')
    [(SheafOfModules.pushforward
      (structureMap (J := J) (K := K) F O)).IsRightAdjoint]
    [(SheafOfModules.restrictScalars
      (underlyingAdjointMap (J := J) (K := K) F g)).IsRightAdjoint]
    [(SheafOfModules.pushforward
      (underlyingMap (J := J) (K := K) F g)).IsRightAdjoint] :
    SheafOfModules.pullback (underlyingMap (J := J) (K := K) F g) ≅
      modulePullback (J := J) (K := K) F O ⋙
        SheafOfModules.ChangeOfRings.extendScalars
          (underlyingAdjointMap (J := J) (K := K) F g) :=
  Adjunction.leftAdjointUniq
    (SheafOfModules.pullbackPushforwardAdjunction
      (underlyingMap (J := J) (K := K) F g))
    (adjunction (J := J) (K := K) F g)

/-- The canonical pullback factorization lifted degreewise to homological complexes. -/
@[stacks 03D6 "complex pullback factorization"]
noncomputable def complexIso
    {ι : Type*} (c : ComplexShape ι)
    (g : O ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u v} J K).obj O')
    [(SheafOfModules.pushforward
      (structureMap (J := J) (K := K) F O)).IsRightAdjoint]
    [(SheafOfModules.restrictScalars
      (underlyingAdjointMap (J := J) (K := K) F g)).IsRightAdjoint]
    [(SheafOfModules.pushforward
      (underlyingMap (J := J) (K := K) F g)).IsRightAdjoint] :
    (SheafOfModules.pullback
        (underlyingMap (J := J) (K := K) F g)).mapHomologicalComplex c ≅
      (modulePullback (J := J) (K := K) F O).mapHomologicalComplex c ⋙
        (SheafOfModules.ChangeOfRings.extendScalars
          (underlyingAdjointMap (J := J) (K := K) F g)).mapHomologicalComplex c :=
  NatIso.mapHomologicalComplex (pullbackIso (J := J) (K := K) F g) c ≪≫
    (Functor.mapHomologicalComplexCompIso
      (F := modulePullback (J := J) (K := K) F O)
      (G := SheafOfModules.ChangeOfRings.extendScalars
        (underlyingAdjointMap (J := J) (K := K) F g))
      (H := modulePullback (J := J) (K := K) F O ⋙
        SheafOfModules.ChangeOfRings.extendScalars
          (underlyingAdjointMap (J := J) (K := K) F g))
      (Iso.refl
        (modulePullback (J := J) (K := K) F O ⋙
          SheafOfModules.ChangeOfRings.extendScalars
            (underlyingAdjointMap (J := J) (K := K) F g))) c).symm

/-- The object component of the canonical pullback factorization on homological complexes. -/
noncomputable def complexObjIso
    {ι : Type*} (c : ComplexShape ι)
    (g : O ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u v} J K).obj O')
    [(SheafOfModules.pushforward
      (structureMap (J := J) (K := K) F O)).IsRightAdjoint]
    [(SheafOfModules.restrictScalars
      (underlyingAdjointMap (J := J) (K := K) F g)).IsRightAdjoint]
    [(SheafOfModules.pushforward
      (underlyingMap (J := J) (K := K) F g)).IsRightAdjoint]
    (L : HomologicalComplex (ringedSiteModuleCategory J O) c) :
    ((SheafOfModules.pullback
      (underlyingMap (J := J) (K := K) F g)).mapHomologicalComplex c).obj L ≅
      ((SheafOfModules.ChangeOfRings.extendScalars
        (underlyingAdjointMap (J := J) (K := K) F g)).mapHomologicalComplex c).obj
          (((modulePullback (J := J) (K := K) F O).mapHomologicalComplex c).obj L) :=
  (complexIso (J := J) (K := K) F c g).app L

section ComplexAPI

variable {ι : Type*} (c : ComplexShape ι)
variable (g : O ⟶ (F.sheafPushforwardContinuous CommRingCat.{max u v} J K).obj O')
variable [(SheafOfModules.pushforward
  (structureMap (J := J) (K := K) F O)).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars
  (underlyingAdjointMap (J := J) (K := K) F g)).IsRightAdjoint]
variable [(SheafOfModules.pushforward
  (underlyingMap (J := J) (K := K) F g)).IsRightAdjoint]

/-- In each degree, the forward complex factorization is the corresponding component of the
module-pullback factorization. -/
@[simp]
theorem complexObjIso_hom_f
    (L : HomologicalComplex (ringedSiteModuleCategory J O) c) (i : ι) :
    (complexObjIso (J := J) (K := K) F c g L).hom.f i =
      (pullbackIso (J := J) (K := K) F g).hom.app (L.X i) := sorry

/-- In each degree, the inverse complex factorization is the corresponding inverse component
of the module-pullback factorization. -/
@[simp]
theorem complexObjIso_inv_f
    (L : HomologicalComplex (ringedSiteModuleCategory J O) c) (i : ι) :
    (complexObjIso (J := J) (K := K) F c g L).inv.f i =
      (pullbackIso (J := J) (K := K) F g).inv.app (L.X i) := sorry

end ComplexAPI

end Factorization

namespace UnderlyingRing

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (F : C ⥤ D) [F.IsContinuous J K]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
variable [K.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
variable [HasWeakSheafify K CommRingCat.{max u v}]
variable [HasWeakSheafify K RingCat.{max u v}]
variable [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
variable [∀ P : Cᵒᵖ ⥤ RingCat.{max u v}, F.op.HasLeftKanExtension P]
variable (O : Sheaf J CommRingCat.{max u v})
variable [(SheafOfModules.pushforward
  (structureMap (J := J) (K := K) F O)).IsRightAdjoint]
variable [(SheafOfModules.pushforward
  (underlyingRingUnit (J := J) (K := K) F O)).IsRightAdjoint]

/-- An identification of the two pulled-back underlying ring sheaves that intertwines their
structure maps induces the corresponding comparison of module pullback functors. -/
noncomputable def pullbackIsoOfIso
    (e : ringSheaf K ((ringPullback (J := J) (K := K) F).obj O) ≅
      underlyingRingPullback (J := J) (K := K) F O)
    (he : structureMap (J := J) (K := K) F O ≫
      (F.sheafPushforwardContinuous RingCat.{max u v} J K).map e.hom =
        underlyingRingUnit (J := J) (K := K) F O) :
    underlyingModulePullback (J := J) (K := K) F O ≅
      modulePullback (J := J) (K := K) F O ⋙
        SheafOfModules.restrictScalars e.inv :=
  SheafOfModules.pullbackIsoOfIso
    (structureMap (J := J) (K := K) F O)
    (underlyingRingUnit (J := J) (K := K) F O) e he

namespace Complex

/-- The comparison of module pullbacks across an identified underlying ring sheaf, lifted to
homological complexes of any shape. -/
noncomputable def mapIsoOfIso
    {ι : Type*} (c : ComplexShape ι)
    (e : ringSheaf K ((ringPullback (J := J) (K := K) F).obj O) ≅
      underlyingRingPullback (J := J) (K := K) F O)
    (he : structureMap (J := J) (K := K) F O ≫
      (F.sheafPushforwardContinuous RingCat.{max u v} J K).map e.hom =
        underlyingRingUnit (J := J) (K := K) F O) :
    (underlyingModulePullback (J := J) (K := K) F O).mapHomologicalComplex c ≅
      (modulePullback (J := J) (K := K) F O).mapHomologicalComplex c ⋙
        (SheafOfModules.restrictScalars e.inv).mapHomologicalComplex c :=
  NatIso.mapHomologicalComplex (pullbackIsoOfIso F O e he) c

/-- The object component of the comparison of module pullbacks on homological complexes. -/
noncomputable def objIsoOfIso
    {ι : Type*} (c : ComplexShape ι)
    (e : ringSheaf K ((ringPullback (J := J) (K := K) F).obj O) ≅
      underlyingRingPullback (J := J) (K := K) F O)
    (he : structureMap (J := J) (K := K) F O ≫
      (F.sheafPushforwardContinuous RingCat.{max u v} J K).map e.hom =
        underlyingRingUnit (J := J) (K := K) F O)
    (L : HomologicalComplex (ringedSiteModuleCategory J O) c) :
    ((underlyingModulePullback (J := J) (K := K) F O).mapHomologicalComplex c).obj L ≅
      ((SheafOfModules.restrictScalars e.inv).mapHomologicalComplex c).obj
        (((modulePullback (J := J) (K := K) F O).mapHomologicalComplex c).obj L) :=
  (mapIsoOfIso F O c e he).app L

/-- In each degree, the forward complex comparison is the component of the module-pullback
comparison on that term. -/
@[simp]
theorem objIsoOfIso_hom_f
    {ι : Type*} (c : ComplexShape ι)
    (e : ringSheaf K ((ringPullback (J := J) (K := K) F).obj O) ≅
      underlyingRingPullback (J := J) (K := K) F O)
    (he : structureMap (J := J) (K := K) F O ≫
      (F.sheafPushforwardContinuous RingCat.{max u v} J K).map e.hom =
        underlyingRingUnit (J := J) (K := K) F O)
    (L : HomologicalComplex (ringedSiteModuleCategory J O) c) (i : ι) :
    (objIsoOfIso F O c e he L).hom.f i =
      (pullbackIsoOfIso F O e he).hom.app (L.X i) := sorry

/-- In each degree, the inverse complex comparison is the inverse component of the
module-pullback comparison on that term. -/
@[simp]
theorem objIsoOfIso_inv_f
    {ι : Type*} (c : ComplexShape ι)
    (e : ringSheaf K ((ringPullback (J := J) (K := K) F).obj O) ≅
      underlyingRingPullback (J := J) (K := K) F O)
    (he : structureMap (J := J) (K := K) F O ≫
      (F.sheafPushforwardContinuous RingCat.{max u v} J K).map e.hom =
        underlyingRingUnit (J := J) (K := K) F O)
    (L : HomologicalComplex (ringedSiteModuleCategory J O) c) (i : ι) :
    (objIsoOfIso F O c e he L).inv.f i =
      (pullbackIsoOfIso F O e he).inv.app (L.X i) := sorry

end Complex

variable [(forget₂ CommRingCat RingCat.{max u v}).PreservesLeftKanExtensions F.op]
variable [K.PreservesSheafification (forget₂ CommRingCat RingCat.{max u v})]

/-- The canonical comparison from direct underlying-ring module pullback to commutative-ring
pullback followed by transport of coefficients. -/
@[stacks 08TM "underlying-ring module pullback"]
noncomputable def pullbackIso :
    underlyingModulePullback (J := J) (K := K) F O ≅
      modulePullback (J := J) (K := K) F O ⋙
        SheafOfModules.restrictScalars
          (ringSheafPullbackIso (J := J) (K := K) F O).inv :=
  pullbackIsoOfIso F O (ringSheafPullbackIso (J := J) (K := K) F O)
    (structureMap_comp_ringSheafPullbackIso_hom (J := J) (K := K) F O)

namespace Complex

/-- The canonical underlying-ring comparison lifted to homological complexes of any shape. -/
@[stacks 08TM "underlying-ring complex pullback"]
noncomputable def mapIso {ι : Type*} (c : ComplexShape ι) :
    (underlyingModulePullback (J := J) (K := K) F O).mapHomologicalComplex c ≅
      (modulePullback (J := J) (K := K) F O).mapHomologicalComplex c ⋙
        (SheafOfModules.restrictScalars
          (ringSheafPullbackIso (J := J) (K := K) F O).inv).mapHomologicalComplex c :=
  mapIsoOfIso F O c
    (ringSheafPullbackIso (J := J) (K := K) F O)
    (structureMap_comp_ringSheafPullbackIso_hom (J := J) (K := K) F O)

/-- The object component of the canonical underlying-ring comparison on homological complexes. -/
@[stacks 08TM "underlying-ring complex component"]
noncomputable def objIso
    {ι : Type*} (c : ComplexShape ι)
    (L : HomologicalComplex (ringedSiteModuleCategory J O) c) :
    ((underlyingModulePullback (J := J) (K := K) F O).mapHomologicalComplex c).obj L ≅
      ((SheafOfModules.restrictScalars
        (ringSheafPullbackIso (J := J) (K := K) F O).inv).mapHomologicalComplex c).obj
          (((modulePullback (J := J) (K := K) F O).mapHomologicalComplex c).obj L) :=
  (mapIso F O c).app L

/-- In each degree, the canonical forward complex comparison is the corresponding component of
the canonical module-pullback comparison. -/
@[simp]
theorem objIso_hom_f
    {ι : Type*} (c : ComplexShape ι)
    (L : HomologicalComplex (ringedSiteModuleCategory J O) c) (i : ι) :
    (objIso (J := J) (K := K) F O c L).hom.f i =
      (pullbackIso (J := J) (K := K) F O).hom.app (L.X i) := sorry

/-- In each degree, the canonical inverse complex comparison is the inverse component of the
canonical module-pullback comparison. -/
@[simp]
theorem objIso_inv_f
    {ι : Type*} (c : ComplexShape ι)
    (L : HomologicalComplex (ringedSiteModuleCategory J O) c) (i : ι) :
    (objIso (J := J) (K := K) F O c L).inv.f i =
      (pullbackIso (J := J) (K := K) F O).inv.app (L.X i) := sorry

end Complex

end UnderlyingRing

end SheafOfModules.RingedSite.InverseImage
