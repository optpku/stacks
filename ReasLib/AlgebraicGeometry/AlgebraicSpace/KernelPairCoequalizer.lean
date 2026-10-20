/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Factorization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Map
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism

/-!
# Kernel-pair coequalizers of proper morphisms

The equalizer algebra of the two kernel-pair projections defines a relative
spectrum with a proper surjective quotient map and a finite universally
injective structure morphism over the locally Noetherian target.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.KernelPairCoequalizer

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The kernel pair `R = Y ×_X Y` of a morphism of algebraic spaces. -/
def relation (g : Y ⟶ X) : AlgebraicSpace S :=
  pullback g g

/-- The kernel pair of `g` is the pullback of `g` along itself. -/
theorem relation_eq_pullback (g : Y ⟶ X) : relation g = pullback g g :=
  rfl

/-- The first projection of the kernel pair. -/
def fst (g : Y ⟶ X) : relation g ⟶ Y :=
  pullback.fst g g

/-- The first kernel-pair projection is `pullback.fst`. -/
theorem fst_eq (g : Y ⟶ X) : fst g = pullback.fst g g :=
  rfl

/-- The second projection of the kernel pair. -/
def snd (g : Y ⟶ X) : relation g ⟶ Y :=
  pullback.snd g g

/-- The second kernel-pair projection is `pullback.snd`. -/
theorem snd_eq (g : Y ⟶ X) : snd g = pullback.snd g g :=
  rfl

/-- The two kernel-pair projections agree after composing with `g`. -/
theorem fst_comp (g : Y ⟶ X) : fst g ≫ g = snd g ≫ g :=
  pullback.condition

/-- The structure morphism `h : R ⟶ X` of the kernel pair, obtained as
`snd g ≫ g`. -/
def toAmbient (g : Y ⟶ X) : relation g ⟶ X :=
  snd g ≫ g

/-- The kernel-pair structure morphism is `snd g ≫ g`. -/
theorem toAmbient_eq (g : Y ⟶ X) : toAmbient g = snd g ≫ g :=
  rfl

/-- The first kernel-pair projection of a proper morphism is proper. -/
instance instProper_fst (g : Y ⟶ X) [Proper g] : Proper (fst g) :=
  Proper.of_isPullback (IsPullback.of_hasPullback g g).flip inferInstance

/-- The second kernel-pair projection of a proper morphism is proper. -/
instance instProper_snd (g : Y ⟶ X) [Proper g] : Proper (snd g) :=
  Proper.pullback_snd inferInstance g

/-- The kernel-pair structure morphism of a proper morphism is proper. -/
instance instProper_toAmbient (g : Y ⟶ X) [Proper g] : Proper (toAmbient g) :=
  proper_comp (snd g) g

/-- The algebra map `g_* 𝒪_Y ⟶ h_* 𝒪_R` induced by the first kernel-pair
projection. -/
def algebraMapFst (g : Y ⟶ X) [Proper g] :
    (pushforwardStructureQcAlgebra g).obj.right ⟶
      (pushforwardStructureQcAlgebra (toAmbient g)).obj.right :=
  (commRingPushforward g).map (commStructureSheafMap (fst g)) ≫
    (commRingPushforwardComp (fst g) g).hom.app
      (commStructureSheaf (relation g)) ≫
    eqToHom
      (congrArg
        (fun p ↦ (commRingPushforward p).obj (commStructureSheaf (relation g)))
        (pullback.condition : fst g ≫ g = snd g ≫ g))

/-- The algebra map `g_* 𝒪_Y ⟶ h_* 𝒪_R` induced by the second kernel-pair
projection. -/
def algebraMapSnd (g : Y ⟶ X) [Proper g] :
    (pushforwardStructureQcAlgebra g).obj.right ⟶
      (pushforwardStructureQcAlgebra (toAmbient g)).obj.right :=
  (commRingPushforward g).map (commStructureSheafMap (snd g)) ≫
    (commRingPushforwardComp (snd g) g).hom.app
      (commStructureSheaf (relation g))

/-- `algebraMapFst` is the pushforward of `fst^♯` followed by the composition
iso and the kernel-pair identification. -/
theorem algebraMapFst_eq (g : Y ⟶ X) [Proper g] :
    algebraMapFst g =
      (commRingPushforward g).map (commStructureSheafMap (fst g)) ≫
        (commRingPushforwardComp (fst g) g).hom.app
          (commStructureSheaf (relation g)) ≫
        eqToHom
          (congrArg
            (fun p ↦
              (commRingPushforward p).obj (commStructureSheaf (relation g)))
            (pullback.condition : fst g ≫ g = snd g ≫ g)) :=
  rfl

/-- `algebraMapSnd` is the pushforward of `snd^♯` followed by the composition
iso. -/
theorem algebraMapSnd_eq (g : Y ⟶ X) [Proper g] :
    algebraMapSnd g =
      (commRingPushforward g).map (commStructureSheafMap (snd g)) ≫
        (commRingPushforwardComp (snd g) g).hom.app
          (commStructureSheaf (relation g)) :=
  rfl

private theorem equalizerPresheaf_map_condition (g : Y ⟶ X) [Proper g]
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
    (equalizer.ι ((algebraMapFst g).hom.app U) ((algebraMapSnd g).hom.app U) ≫
        (pushforwardStructureQcAlgebra g).obj.right.obj.map i) ≫
        (algebraMapFst g).hom.app V =
      (equalizer.ι ((algebraMapFst g).hom.app U) ((algebraMapSnd g).hom.app U) ≫
        (pushforwardStructureQcAlgebra g).obj.right.obj.map i) ≫
        (algebraMapSnd g).hom.app V :=
  sorry

private def equalizerPresheafMap (g : Y ⟶ X) [Proper g]
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
    equalizer ((algebraMapFst g).hom.app U) ((algebraMapSnd g).hom.app U) ⟶
      equalizer ((algebraMapFst g).hom.app V) ((algebraMapSnd g).hom.app V) :=
  equalizer.lift
    (equalizer.ι ((algebraMapFst g).hom.app U) ((algebraMapSnd g).hom.app U) ≫
      (pushforwardStructureQcAlgebra g).obj.right.obj.map i)
    (equalizerPresheaf_map_condition g i)

private theorem equalizerPresheaf_map_id (g : Y ⟶ X) [Proper g]
    (U : (smallEtaleSite X)ᵒᵖ) : equalizerPresheafMap g (𝟙 U) = 𝟙 _ :=
  sorry

private theorem equalizerPresheaf_map_comp (g : Y ⟶ X) [Proper g]
    {U V W : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    equalizerPresheafMap g (i ≫ j) = equalizerPresheafMap g i ≫ equalizerPresheafMap g j :=
  sorry

/-- The pointwise equalizer of the two kernel-pair algebra maps, as a
commutative-ring presheaf on the small étale site of `X`. -/
def equalizerPresheaf (g : Y ⟶ X) [Proper g] :
    (smallEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u} where
  obj U := equalizer ((algebraMapFst g).hom.app U) ((algebraMapSnd g).hom.app U)
  map {U V} i :=
    equalizer.lift
      (equalizer.ι ((algebraMapFst g).hom.app U) ((algebraMapSnd g).hom.app U) ≫
        (pushforwardStructureQcAlgebra g).obj.right.obj.map i)
      (by exact equalizerPresheaf_map_condition g i)
  map_id := by
    intro U
    exact equalizerPresheaf_map_id g U
  map_comp := by
    intro U V W i j
    exact equalizerPresheaf_map_comp g i j

/-- The underlying functor of `equalizerPresheaf` evaluates to the pointwise
equalizer of the kernel-pair algebra maps. -/
theorem equalizerPresheaf_obj (g : Y ⟶ X) [Proper g] (U : (smallEtaleSite X)ᵒᵖ) :
    (equalizerPresheaf g).obj U =
      equalizer ((algebraMapFst g).hom.app U) ((algebraMapSnd g).hom.app U) :=
  rfl

private theorem equalizerSheaf_isSheaf (g : Y ⟶ X) [Proper g] :
    Presheaf.IsSheaf (smallEtaleTopology X) (equalizerPresheaf g) :=
  sorry

/-- The equalizer of the kernel-pair algebra maps, as a sheaf of commutative
rings on the small étale site of `X`. -/
def equalizerSheaf (g : Y ⟶ X) [Proper g] :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} where
  obj := equalizerPresheaf g
  property := by exact equalizerSheaf_isSheaf g

/-- The underlying presheaf of `equalizerSheaf` is `equalizerPresheaf`. -/
theorem equalizerSheaf_obj (g : Y ⟶ X) [Proper g] :
    (equalizerSheaf g).obj = equalizerPresheaf g :=
  rfl

private theorem equalizerStructureMap_condition (g : Y ⟶ X) [Proper g]
    (U : (smallEtaleSite X)ᵒᵖ) :
    (commStructureSheafMap g).hom.app U ≫ (algebraMapFst g).hom.app U =
      (commStructureSheafMap g).hom.app U ≫ (algebraMapSnd g).hom.app U :=
  sorry

private def equalizerStructureMapApp (g : Y ⟶ X) [Proper g]
    (U : (smallEtaleSite X)ᵒᵖ) :
    (commStructureSheaf X).obj.obj U ⟶ (equalizerSheaf g).obj.obj U :=
  equalizer.lift ((commStructureSheafMap g).hom.app U)
    (equalizerStructureMap_condition g U)

private theorem equalizerStructureMap_naturality (g : Y ⟶ X) [Proper g]
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
    (commStructureSheaf X).obj.map i ≫ equalizerStructureMapApp g V =
      equalizerStructureMapApp g U ≫ (equalizerSheaf g).obj.map i :=
  sorry

/-- The structure map from `𝒪_X` to the kernel-pair equalizer sheaf. -/
def equalizerStructureMap (g : Y ⟶ X) [Proper g] :
    commStructureSheaf X ⟶ equalizerSheaf g :=
  InducedCategory.homMk
    { app := fun U ↦
        equalizer.lift ((commStructureSheafMap g).hom.app U)
          (by exact equalizerStructureMap_condition g U)
      naturality := by
        intro U V i
        exact equalizerStructureMap_naturality g i }

private theorem equalizerAlgebra_isQuasicoherent (g : Y ⟶ X)
    [IsLocallyNoetherian X] [Proper g] :
    qcAlgebraUnderProperty X (Under.mk (equalizerStructureMap g)) :=
  sorry

/-- The quasi-coherent `𝒪_X`-algebra `𝒜` equalizing the two kernel-pair algebra
maps of a proper morphism `g`. -/
def equalizerAlgebra (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g] :
    X.QcAlgebraUnder where
  obj := Under.mk (equalizerStructureMap g)
  property := by exact equalizerAlgebra_isQuasicoherent g

/-- The sheaf of `equalizerAlgebra` is the kernel-pair equalizer sheaf. -/
theorem equalizerAlgebra_sheaf (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g] :
    (equalizerAlgebra g).obj.right = equalizerSheaf g :=
  rfl

/-- The two kernel-pair algebra maps agree after restriction along the equalizer
inclusion. -/
theorem equalizerAlgebra_spec (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g]
    (U : (smallEtaleSite X)ᵒᵖ) :
    equalizer.ι ((algebraMapFst g).hom.app U) ((algebraMapSnd g).hom.app U) ≫
        (algebraMapFst g).hom.app U =
      equalizer.ι ((algebraMapFst g).hom.app U) ((algebraMapSnd g).hom.app U) ≫
        (algebraMapSnd g).hom.app U :=
  equalizer.condition _ _

private theorem inclusion_naturality (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g]
    {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
    (equalizerSheaf g).obj.map i ≫
        equalizer.ι ((algebraMapFst g).hom.app V) ((algebraMapSnd g).hom.app V) =
      equalizer.ι ((algebraMapFst g).hom.app U) ((algebraMapSnd g).hom.app U) ≫
        (pushforwardStructureQcAlgebra g).obj.right.obj.map i :=
  sorry

private theorem inclusion_commutes (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g] :
    equalizerStructureMap g ≫ InducedCategory.homMk
      { app := fun U ↦
          equalizer.ι ((algebraMapFst g).hom.app U) ((algebraMapSnd g).hom.app U)
        naturality := by
          intro U V i
          exact inclusion_naturality g i } =
      (pushforwardStructureQcAlgebra g).obj.hom :=
  sorry

/-- The inclusion of the kernel-pair equalizer algebra into `g_* 𝒪_Y`. -/
def inclusion (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g] :
    equalizerAlgebra g ⟶ pushforwardStructureQcAlgebra g :=
  InducedCategory.homMk
    (Under.homMk
      (InducedCategory.homMk
        { app := fun U ↦
            equalizer.ι ((algebraMapFst g).hom.app U) ((algebraMapSnd g).hom.app U)
          naturality := by
            intro U V i
            exact inclusion_naturality g i })
      (by exact inclusion_commutes g))

/-- On sections, `inclusion g` is the equalizer inclusion of the two kernel-pair
algebra maps. -/
theorem inclusion_app (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g]
    (U : (smallEtaleSite X)ᵒᵖ) :
    (InducedCategory.Hom.hom (inclusion g).hom.right).app U =
      equalizer.ι ((algebraMapFst g).hom.app U) ((algebraMapSnd g).hom.app U) :=
  rfl

/-- The coequalizer `X'` of the kernel pair of a proper morphism `g : Y ⟶ X`, as
the relative spectrum of the equalizer algebra. -/
def space (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g] : AlgebraicSpace S :=
  relativeSpec (equalizerAlgebra g)

/-- The kernel-pair coequalizer is the relative spectrum of `equalizerAlgebra`. -/
theorem space_eq_relativeSpec (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g] :
    space g = relativeSpec (equalizerAlgebra g) :=
  rfl

/-- The structure morphism `X' ⟶ X` of the kernel-pair coequalizer. -/
def toTarget (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g] : space g ⟶ X :=
  relativeSpecπ (equalizerAlgebra g)

/-- The structure morphism of the kernel-pair coequalizer is the relative-spectrum
projection of `equalizerAlgebra`. -/
theorem toTarget_eq_relativeSpecπ (g : Y ⟶ X) [IsLocallyNoetherian X]
    [Proper g] : toTarget g = relativeSpecπ (equalizerAlgebra g) :=
  rfl

/-- The canonical morphism `Y ⟶ X'` through the relative spectrum of `g_* 𝒪_Y`
and the equalizer inclusion. -/
def fromSource (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g] : Y ⟶ space g :=
  Hom.toPushforwardRelativeSpec g ≫ relativeSpecMap (inclusion g)

/-- The source morphism of the kernel-pair coequalizer is the composite of
`Hom.toPushforwardRelativeSpec` with `relativeSpecMap` of the equalizer
inclusion. -/
theorem fromSource_eq (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g] :
    fromSource g =
      Hom.toPushforwardRelativeSpec g ≫ relativeSpecMap (inclusion g) :=
  rfl

/-- The factorization identity `fromSource g ≫ toTarget g = g`. -/
theorem fromSource_comp_toTarget (g : Y ⟶ X) [IsLocallyNoetherian X]
    [Proper g] : fromSource g ≫ toTarget g = g :=
  sorry

/-- The kernel-pair projections equalize `fromSource g`. -/
theorem equalizes (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g] :
    fst g ≫ fromSource g = snd g ≫ fromSource g :=
  sorry

/-- The cofork `R ⇉ Y ⟶ X'` presenting the kernel-pair coequalizer candidate. -/
def cofork (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g] :
    Cofork (fst g) (snd g) :=
  Cofork.ofπ (fromSource g) (equalizes g)

/-- The coequalizer candidate of `cofork g` is `fromSource g`. -/
theorem cofork_π (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g] :
    (cofork g).π = fromSource g :=
  rfl

/-- For a proper morphism with locally Noetherian target, every morphism
constant on its kernel pair factors uniquely through the relative spectrum of
the kernel-pair equalizer algebra. -/
@[stacks 0AGG]
theorem isCoequalizer (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g]
    {Z : AlgebraicSpace S} (φ : Y ⟶ Z) (h_equalizes : fst g ≫ φ = snd g ≫ φ) :
    ∃! ψ : space g ⟶ Z, fromSource g ≫ ψ = φ :=
  sorry

/-- The structure morphism of the kernel-pair coequalizer is finite. -/
@[stacks 0AGG, instance]
instance instIsFinite_toTarget (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g] :
    IsFinite (toTarget g) :=
  sorry

/-- The canonical morphism to the kernel-pair coequalizer is proper. -/
@[stacks 0AGG, instance]
instance instProper_fromSource (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g] :
    Proper (fromSource g) :=
  sorry

/-- The canonical morphism to the kernel-pair coequalizer is surjective. -/
@[stacks 0AGG, instance]
instance instSurjective_fromSource (g : Y ⟶ X) [IsLocallyNoetherian X]
    [Proper g] : Surjective (fromSource g) :=
  sorry

/-- The structure morphism of the kernel-pair coequalizer is universally injective. -/
@[stacks 0AGG, instance]
instance instUniversallyInjective_toTarget (g : Y ⟶ X) [IsLocallyNoetherian X]
    [Proper g] : UniversallyInjective (toTarget g) :=
  sorry

/-- For a surjective proper morphism with locally Noetherian target, the structure
morphism of its kernel-pair coequalizer is a universal homeomorphism. -/
@[stacks 0AGG, instance]
instance instUniversalHomeomorphism_toTarget (g : Y ⟶ X) [IsLocallyNoetherian X]
    [Proper g] [Surjective g] : UniversalHomeomorphism (toTarget g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.KernelPairCoequalizer
