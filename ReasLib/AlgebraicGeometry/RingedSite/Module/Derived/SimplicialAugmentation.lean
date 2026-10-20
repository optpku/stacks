/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.SimplicialLowerShriek
public import ReasLib.CategoryTheory.Localization.FormalIso
public import ReasLib.AlgebraicTopology.SimplicialObject.Augmentation
public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.AlternatingFace
import Mathlib.Tactic.CrossRefAttribute

/-!
# Augmented simplicial ring sheaves

An augmentation of a simplicial ring sheaf to a constant ring sheaf produces a module-valued
derived lower shriek with a comparison to the derived lower shriek of additive sheaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

-- The exposed comparisons use private formal reverse-component implementations.
set_option backward.privateInPublic true

universe u v w

namespace CategoryTheory.SimplicialSite.Derived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [UnivLE.{max u v, w}]
variable [HasSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasSheafify (SimplicialSite.topology J) AddCommGrpCat.{w}]
variable [GrothendieckTopology.WEqualsLocallyBijective
  (SimplicialSite.topology J) AddCommGrpCat.{w}]
variable [GrothendieckTopology.HasSheafCompose (SimplicialSite.topology J)
  (forget₂ CommRingCat.{w} RingCat.{w})]
variable [Functor.IsRightAdjoint
  (siteAbelianInverseImageDerived (SimplicialSite.topology J) J
    SimplicialSite.projection)]

/-- The constant simplicial commutative-ring sheaf associated to `𝒪`. -/
@[stacks 09D3 "constant simplicial structure sheaf"]
abbrev constantStructureSheaf (𝒪 : Sheaf J CommRingCat.{w}) :
    SimplicialObject (Sheaf J CommRingCat.{w}) :=
  (SimplicialObject.const (Sheaf J CommRingCat.{w})).obj 𝒪

/-- The associated sheaf of a constant simplicial sheaf is definitionally the inverse image along
the simplicial-site projection; the displayed isomorphism is therefore `Iso.refl`. -/
@[stacks 09D3 "constant simplicial sheaf comparison"]
def constantProjectionIso (𝒪 : Sheaf J CommRingCat.{w}) :
    SimplicialSite.ringSheaf (constantStructureSheaf 𝒪) ≅
      (SimplicialSite.projection.sheafPushforwardContinuous CommRingCat.{w}
        (SimplicialSite.topology J) J).obj 𝒪 :=
  Iso.refl _

/-- The module-valued derived lower shriek in the constant-coefficient case. -/
@[stacks 09D3 "constant-coefficient module lower shriek"]
noncomputable abbrev constantLowerShriek (𝒪 : Sheaf J CommRingCat.{w})
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Cocontinuous.moduleLowerShriek.toDerived
        (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
        (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪))
      (RingedSite.Hom.ModuleQis.{w}
        (RingedSite.Cocontinuous.moduleInverseImage.source
          (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
          (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪)))] :
    RingedSite.Hom.ModuleDerived.{w}
        (RingedSite.ofCommRingSheaf (SimplicialSite.topology J)
          (SimplicialSite.ringSheaf (constantStructureSheaf 𝒪))) ⥤
      RingedSite.Hom.ModuleDerived.{w}
        (RingedSite.ofCommRingSheaf J 𝒪) :=
  RingedSite.Cocontinuous.moduleLowerShriek.derived
    (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
    (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪)

/-- Forgetting the module structure on the target of `constantLowerShriek`. -/
@[stacks 09D3 "constant-coefficient derived forgetful functor"]
noncomputable abbrev constantForget (𝒪 : Sheaf J CommRingCat.{w}) :
    RingedSite.Hom.ModuleDerived.{w} (RingedSite.ofCommRingSheaf J 𝒪) ⥤
      DerivedCategory (Sheaf J AddCommGrpCat.{w}) :=
  RingedSite.Hom.underlyingAbelianSheafDerived (RingedSite.ofCommRingSheaf J 𝒪)

set_option maxHeartbeats 2000000 in
/-- The canonical derived comparison from the additive projection lower shriek to the
constant-coefficient module lower shriek followed by forgetting. -/
@[stacks 09D3 "constant lower-shriek underlying comparison"]
noncomputable abbrev constantLowerShriek.underlyingComparison
    (𝒪 : Sheaf J CommRingCat.{w})
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Cocontinuous.moduleLowerShriek.toDerived
        (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
        (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪))
      (RingedSite.Hom.ModuleQis.{w}
        (RingedSite.Cocontinuous.moduleInverseImage.source
          (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
          (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪)))]
    [RingedSite.Cocontinuous.moduleLowerShriek.derived.HasPair
      (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
      (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪)] :
    lowerShriek (constantStructureSheaf 𝒪) ⟶
      constantLowerShriek 𝒪 ⋙ constantForget 𝒪 :=
  RingedSite.Cocontinuous.moduleLowerShriek.derived.underlyingComparison
    (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
    (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪)

section ConstantComparison

variable (𝒪 : Sheaf J CommRingCat.{w})
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Cocontinuous.moduleLowerShriek.toDerived
        (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
        (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪))
      (RingedSite.Hom.ModuleQis.{w}
        (RingedSite.Cocontinuous.moduleInverseImage.source
          (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
          (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪)))]
    [RingedSite.Cocontinuous.moduleLowerShriek.derived.HasPair
      (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
      (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪)]

namespace constantLowerShriek

/-- Every component of the constant-coefficient comparison has a quasi-isomorphic homotopy representative. -/
theorem underlyingComparison_quasiIso
    (K : RingedSite.Hom.ModuleDerived.{w}
      (RingedSite.ofCommRingSheaf (SimplicialSite.topology J)
        (SimplicialSite.ringSheaf (constantStructureSheaf 𝒪)))) :
    HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{w}) (ComplexShape.up ℤ)
      (Localization.arrowRepresentative DerivedCategory.Qh
        ((underlyingComparison 𝒪).app K)).hom :=
  sorry

/-- The reverse component is the formal inverse of the comparison's specified homotopy representative. -/
private def underlyingComparisonInvApp
    (K : RingedSite.Hom.ModuleDerived.{w}
      (RingedSite.ofCommRingSheaf (SimplicialSite.topology J)
        (SimplicialSite.ringSheaf (constantStructureSheaf 𝒪)))) :
    (constantLowerShriek 𝒪 ⋙ constantForget 𝒪).obj K ⟶
      (lowerShriek (constantStructureSheaf 𝒪)).obj K :=
  (Localization.formalIsoOfArrowRepresentative
    (HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{w}) (ComplexShape.up ℤ))
    DerivedCategory.Qh ((underlyingComparison 𝒪).app K)
    (underlyingComparison_quasiIso 𝒪 K)).inv

/-- The formal reverse components are natural and are two-sided inverses to the comparison. -/
theorem underlyingComparison_inverse_laws :
    (∀ {K K'} (f : K ⟶ K'),
      (constantLowerShriek 𝒪 ⋙ constantForget 𝒪).map f ≫
          underlyingComparisonInvApp 𝒪 K' =
        underlyingComparisonInvApp 𝒪 K ≫
          (lowerShriek (constantStructureSheaf 𝒪)).map f) ∧
    (∀ K, (underlyingComparison 𝒪).app K ≫
      underlyingComparisonInvApp 𝒪 K = 𝟙 _) ∧
    (∀ K, underlyingComparisonInvApp 𝒪 K ≫
      (underlyingComparison 𝒪).app K = 𝟙 _) :=
  sorry

/-- The reverse constant-coefficient comparison has the specified formal inverse components. -/
def underlyingComparisonInv :
    constantLowerShriek 𝒪 ⋙ constantForget 𝒪 ⟶
      lowerShriek (constantStructureSheaf 𝒪) where
  app := underlyingComparisonInvApp 𝒪
  naturality := fun {K K'} f =>
    (underlyingComparison_inverse_laws 𝒪).1 (K := K) (K' := K') f

/-- The canonical constant-coefficient comparison and its formal reverse form a natural isomorphism. -/
@[stacks 09D3 "constant lower-shriek underlying natural isomorphism"]
def underlyingComparisonIso :
    lowerShriek (constantStructureSheaf 𝒪) ≅
      constantLowerShriek 𝒪 ⋙ constantForget 𝒪 where
  hom := underlyingComparison 𝒪
  inv := underlyingComparisonInv 𝒪
  hom_inv_id := by
    ext K
    simpa only [NatTrans.comp_app, NatTrans.id_app, underlyingComparisonInv] using
      (underlyingComparison_inverse_laws 𝒪).2.1 K
  inv_hom_id := by
    ext K
    simpa only [NatTrans.comp_app, NatTrans.id_app, underlyingComparisonInv] using
      (underlyingComparison_inverse_laws 𝒪).2.2 K

/-- The constant-coefficient comparison is invertible with its specified formal reverse. -/
@[stacks 09D3 "constant lower-shriek underlying comparison isomorphism"]
theorem underlyingComparison_isIso :
    IsIso (underlyingComparison 𝒪) :=
  (underlyingComparisonIso 𝒪).isIso_hom

end constantLowerShriek

end ConstantComparison

/-- In the constant case, forgetting module structure recovers the projection lower shriek. -/
@[stacks 09D3 "constant lower-shriek forgetful comparison"]
theorem constantLowerShriek.forget_isomorphic
    (𝒪 : Sheaf J CommRingCat.{w})
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Cocontinuous.moduleLowerShriek.toDerived
        (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
        (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪))
      (RingedSite.Hom.ModuleQis.{w}
        (RingedSite.Cocontinuous.moduleInverseImage.source
          (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
          (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪)))] :
    IsIsomorphic (lowerShriek (constantStructureSheaf 𝒪))
      (constantLowerShriek 𝒪 ⋙ constantForget 𝒪) := sorry

/-- The constant-coefficient module lower shriek inherits the canonical integer-shift comparison
from the site-generic derived lower shriek. -/
@[stacks 09D3 "constant lower shriek shift", implicit_reducible]
noncomputable def constantLowerShriek.commShift
    (𝒪 : Sheaf J CommRingCat.{w})
    [Functor.HasPointwiseLeftDerivedFunctor
      (RingedSite.Cocontinuous.moduleLowerShriek.toDerived
        (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
        (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪))
      (RingedSite.Hom.ModuleQis.{w}
        (RingedSite.Cocontinuous.moduleInverseImage.source
          (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
          (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪)))] :
    (constantLowerShriek 𝒪).CommShift ℤ :=
  RingedSite.Cocontinuous.moduleLowerShriek.derived.commShift
    (f := SimplicialSite.projection)
    (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪)

/-- The constant-coefficient module lower shriek is exact for its canonical shift comparison. -/
@[stacks 09D3 "constant lower shriek is triangulated"]
theorem constantLowerShriek.isTriangulated
    (𝒪 : Sheaf J CommRingCat.{w})
    [Functor.HasPointwiseLeftDerivedFunctor
      (RingedSite.Cocontinuous.moduleLowerShriek.toDerived
        (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
        (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪))
      (RingedSite.Hom.ModuleQis.{w}
        (RingedSite.Cocontinuous.moduleInverseImage.source
          (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
          (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪)))] :
    @Functor.IsTriangulated _ _ _ _ _ _ (constantLowerShriek 𝒪)
      (constantLowerShriek.commShift 𝒪) _ _ _ _ _ _ _ _ := sorry

omit [UnivLE.{max u v, w}] in
/-- Forgetting rings and multiplication gives the additive sheaf used by the augmentation
complex. -/
@[stacks 09D3 "underlying additive sheaf"]
abbrev additiveSheaf :
    Sheaf J CommRingCat.{w} ⥤ Sheaf J AddCommGrpCat.{w} :=
  sheafCompose J
    (forget₂ CommRingCat.{w} RingCat.{w} ⋙
      forget₂ RingCat.{w} AddCommGrpCat.{w})

omit [UnivLE.{max u v, w}] in
/-- A ring-valued augmentation regarded as an augmentation of additive sheaves. -/
@[stacks 09D3 "underlying additive augmentation"]
abbrev additiveAugmentation
    {A : SimplicialObject (Sheaf J CommRingCat.{w})}
    {𝒪 : Sheaf J CommRingCat.{w}}
    (ε : A ⟶ constantStructureSheaf 𝒪) :
    SimplicialObject.Augmented (Sheaf J AddCommGrpCat.{w}) :=
  (SimplicialObject.Augmented.whiskeringObj
    (Sheaf J CommRingCat.{w}) (Sheaf J AddCommGrpCat.{w})
      additiveSheaf).obj
    (SimplicialObject.Augmentation.toAugmented ε)

/-- The alternating-face complex map induced by an augmentation. -/
@[stacks 09D3 "augmentation complex map"]
abbrev augmentationComplexMap
    {A : SimplicialObject (Sheaf J CommRingCat.{w})}
    {𝒪 : Sheaf J CommRingCat.{w}}
    (ε : A ⟶ constantStructureSheaf 𝒪) :=
  AlgebraicTopology.AlternatingFaceMapComplex.ε.app (additiveAugmentation ε)

/-- The module-valued derived lower shriek attached to an augmentation. -/
@[stacks 09D3 "augmentation module lower shriek"]
noncomputable abbrev augmentationLowerShriek
    {A : SimplicialObject (Sheaf J CommRingCat.{w})}
    {𝒪 : Sheaf J CommRingCat.{w}}
    (ε : A ⟶ constantStructureSheaf 𝒪)
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Cocontinuous.moduleLowerShriek.toDerived
        (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
        (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪))
      (RingedSite.Hom.ModuleQis.{w}
        (RingedSite.Cocontinuous.moduleInverseImage.source
          (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
          (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪)))] :
    RingedSite.Hom.ModuleDerived.{w}
        (RingedSite.ofCommRingSheaf (SimplicialSite.topology J)
          (SimplicialSite.ringSheaf A)) ⥤
      RingedSite.Hom.ModuleDerived.{w}
        (RingedSite.ofCommRingSheaf J 𝒪) :=
  tensor ε ⋙ constantLowerShriek 𝒪

/-- A quasi-isomorphic augmentation makes the source unit comparison invertible. -/
@[stacks 09D3 "augmentation unit comparison"]
theorem unitComparison.isIso
    {A : SimplicialObject (Sheaf J CommRingCat.{w})}
    {𝒪 : Sheaf J CommRingCat.{w}}
    (ε : A ⟶ constantStructureSheaf 𝒪)
    [QuasiIso (augmentationComplexMap ε)] :
    IsIso (unitComparison ε) := sorry

/-- The forgetful functor comparison for an augmentation whose unit comparison is already known
to be invertible. -/
@[stacks 09D3 "augmentation lower-shriek comparison from unit isomorphism"]
theorem augmentationLowerShriek.forget_isomorphic_of_unit
    {A : SimplicialObject (Sheaf J CommRingCat.{w})}
    {𝒪 : Sheaf J CommRingCat.{w}}
    (ε : A ⟶ constantStructureSheaf 𝒪)
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Cocontinuous.moduleLowerShriek.toDerived
        (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
        (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪))
      (RingedSite.Hom.ModuleQis.{w}
        (RingedSite.Cocontinuous.moduleInverseImage.source
          (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
          (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪)))]
    [IsIso (unitComparison ε)] :
    IsIsomorphic (lowerShriek A) (augmentationLowerShriek ε ⋙ constantForget 𝒪) := sorry

/-- The objectwise form of the comparison from an invertible unit comparison. -/
@[stacks 09D3 "objectwise augmentation comparison from unit isomorphism"]
theorem augmentationLowerShriek.forget_obj_isomorphic_of_unit
    {A : SimplicialObject (Sheaf J CommRingCat.{w})}
    {𝒪 : Sheaf J CommRingCat.{w}}
    (ε : A ⟶ constantStructureSheaf 𝒪)
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Cocontinuous.moduleLowerShriek.toDerived
        (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
        (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪))
      (RingedSite.Hom.ModuleQis.{w}
        (RingedSite.Cocontinuous.moduleInverseImage.source
          (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
          (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪)))]
    [IsIso (unitComparison ε)]
    (K : RingedSite.Hom.ModuleDerived.{w}
      (RingedSite.ofCommRingSheaf (SimplicialSite.topology J)
        (SimplicialSite.ringSheaf A))) :
    IsIsomorphic ((lowerShriek A).obj K)
      ((augmentationLowerShriek ε ⋙ constantForget 𝒪).obj K) := sorry

/-- After forgetting the target module structure, augmentation lower shriek agrees with the
additive projection lower shriek. -/
@[stacks 09D3 "augmentation lower-shriek forgetful comparison"]
theorem augmentationLowerShriek.forget_isomorphic
    {A : SimplicialObject (Sheaf J CommRingCat.{w})}
    {𝒪 : Sheaf J CommRingCat.{w}}
    (ε : A ⟶ constantStructureSheaf 𝒪)
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Cocontinuous.moduleLowerShriek.toDerived
        (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
        (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪))
      (RingedSite.Hom.ModuleQis.{w}
        (RingedSite.Cocontinuous.moduleInverseImage.source
          (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
          (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪)))]
    [QuasiIso (augmentationComplexMap ε)] :
    IsIsomorphic (lowerShriek A) (augmentationLowerShriek ε ⋙ constantForget 𝒪) := sorry

/-- The forgetful comparison evaluated at one derived module. -/
@[stacks 09D3 "objectwise augmentation lower-shriek comparison"]
theorem augmentationLowerShriek.forget_obj_isomorphic
    {A : SimplicialObject (Sheaf J CommRingCat.{w})}
    {𝒪 : Sheaf J CommRingCat.{w}}
    (ε : A ⟶ constantStructureSheaf 𝒪)
    [Functor.HasLeftDerivedFunctor
      (RingedSite.Cocontinuous.moduleLowerShriek.toDerived
        (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
        (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪))
      (RingedSite.Hom.ModuleQis.{w}
        (RingedSite.Cocontinuous.moduleInverseImage.source
          (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
          (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪)))]
    [QuasiIso (augmentationComplexMap ε)]
    (K : RingedSite.Hom.ModuleDerived.{w}
      (RingedSite.ofCommRingSheaf (SimplicialSite.topology J)
        (SimplicialSite.ringSheaf A))) :
    IsIsomorphic ((lowerShriek A).obj K)
      ((augmentationLowerShriek ε ⋙ constantForget 𝒪).obj K) := sorry

/-- The augmentation lower shriek inherits the canonical shift comparison from derived change of
rings and constant-coefficient lower shriek. -/
@[stacks 09D3 "augmentation lower shriek shift", implicit_reducible]
noncomputable def augmentationLowerShriek.commShift
    {A : SimplicialObject (Sheaf J CommRingCat.{w})}
    {𝒪 : Sheaf J CommRingCat.{w}}
    (ε : A ⟶ constantStructureSheaf 𝒪)
    [Functor.HasPointwiseLeftDerivedFunctor
      (RingedSite.Cocontinuous.moduleLowerShriek.toDerived
        (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
        (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪))
      (RingedSite.Hom.ModuleQis.{w}
        (RingedSite.Cocontinuous.moduleInverseImage.source
          (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
          (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪)))] :
    (augmentationLowerShriek ε).CommShift ℤ :=
  @Functor.CommShift.comp _ _ _ _ _ _ (tensor ε) (constantLowerShriek 𝒪)
    ℤ _ _ _ _ (tensor.commShift ε) (constantLowerShriek.commShift 𝒪)

/-- The augmentation lower shriek is exact for its canonical shift comparison. -/
@[stacks 09D3 "augmentation lower shriek is triangulated"]
theorem augmentationLowerShriek.isTriangulated
    {A : SimplicialObject (Sheaf J CommRingCat.{w})}
    {𝒪 : Sheaf J CommRingCat.{w}}
    (ε : A ⟶ constantStructureSheaf 𝒪)
    [Functor.HasPointwiseLeftDerivedFunctor
      (RingedSite.Cocontinuous.moduleLowerShriek.toDerived
        (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
        (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪))
      (RingedSite.Hom.ModuleQis.{w}
        (RingedSite.Cocontinuous.moduleInverseImage.source
          (J := SimplicialSite.topology J) (K := J) SimplicialSite.projection
          (_root_.SheafOfModules.RingedSite.ringSheaf J 𝒪)))] :
    @Functor.IsTriangulated _ _ _ _ _ _ (augmentationLowerShriek ε)
      (augmentationLowerShriek.commShift ε) _ _ _ _ _ _ _ _ := sorry

end CategoryTheory.SimplicialSite.Derived
