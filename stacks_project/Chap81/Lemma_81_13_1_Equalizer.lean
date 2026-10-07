module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_40_3_Pullback
public import stacks_project.Chap67.Lemma_67_40_4
public import stacks_project.Chap67.Definition_67_48_3_IntegralClosure
public import stacks_project.Chap76.Lemma_76_6_3_Map

/-!
# Kernel-pair equalizer algebras of proper morphisms

For a proper morphism `g : Y ⟶ X` of algebraic spaces, the kernel pair
`R = Y ×_X Y` induces two `𝒪_X`-algebra maps `g_* 𝒪_Y ⇉ h_* 𝒪_R`. Their
equalizer is a quasi-coherent `𝒪_X`-algebra.
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

/-- The first projection of the kernel pair, corresponding to the Stacks
morphism `t : R ⟶ Y`. -/
def fst (g : Y ⟶ X) : relation g ⟶ Y :=
  pullback.fst g g

/-- The first kernel-pair projection is `pullback.fst`. -/
theorem fst_eq (g : Y ⟶ X) : fst g = pullback.fst g g :=
  rfl

/-- The second projection of the kernel pair, corresponding to the Stacks
morphism `s : R ⟶ Y`. -/
def snd (g : Y ⟶ X) : relation g ⟶ Y :=
  pullback.snd g g

/-- The second kernel-pair projection is `pullback.snd`. -/
theorem snd_eq (g : Y ⟶ X) : snd g = pullback.snd g g :=
  rfl

/-- The two kernel-pair projections agree after composing with `g`. -/
theorem fst_comp (g : Y ⟶ X) : fst g ≫ g = snd g ≫ g :=
  sorry

/-- The structure morphism `h : R ⟶ X` of the kernel pair, obtained as
`snd g ≫ g`. -/
def toAmbient (g : Y ⟶ X) : relation g ⟶ X :=
  snd g ≫ g

/-- The kernel-pair structure morphism is `snd g ≫ g`. -/
theorem toAmbient_eq (g : Y ⟶ X) : toAmbient g = snd g ≫ g :=
  rfl

/-- The first kernel-pair projection of a proper morphism is proper. -/
instance instProper_fst (g : Y ⟶ X) [Proper g] : Proper (fst g) :=
  sorry

/-- The second kernel-pair projection of a proper morphism is proper. -/
instance instProper_snd (g : Y ⟶ X) [Proper g] : Proper (snd g) :=
  sorry

/-- The kernel-pair structure morphism of a proper morphism is proper. -/
instance instProper_toAmbient (g : Y ⟶ X) [Proper g] : Proper (toAmbient g) :=
  sorry

/-- The algebra map `g_* 𝒪_Y ⟶ h_* 𝒪_R` induced by the first kernel-pair
projection. -/
def algebraMapFst (g : Y ⟶ X) [Proper g] :
    (pushforwardStructureQcAlgebra g).obj.right ⟶
      (pushforwardStructureQcAlgebra (toAmbient g)).obj.right :=
  (commRingPushforward g).map (commRingStructureSheafMap (fst g)) ≫
    (ConormalAlgebra.commRingPushforwardCompIso (fst g) g).hom.app
      (commRingStructureSheaf (relation g)) ≫
    eqToHom
      (congrArg
        (fun p ↦ (commRingPushforward p).obj (commRingStructureSheaf (relation g)))
        (pullback.condition : fst g ≫ g = snd g ≫ g))

/-- The algebra map `g_* 𝒪_Y ⟶ h_* 𝒪_R` induced by the second kernel-pair
projection. -/
def algebraMapSnd (g : Y ⟶ X) [Proper g] :
    (pushforwardStructureQcAlgebra g).obj.right ⟶
      (pushforwardStructureQcAlgebra (toAmbient g)).obj.right :=
  (commRingPushforward g).map (commRingStructureSheafMap (snd g)) ≫
    (ConormalAlgebra.commRingPushforwardCompIso (snd g) g).hom.app
      (commRingStructureSheaf (relation g))

/-- `algebraMapFst` is the pushforward of `fst^♯` followed by the composition
iso and the kernel-pair identification. -/
theorem algebraMapFst_eq (g : Y ⟶ X) [Proper g] :
    algebraMapFst g =
      (commRingPushforward g).map (commRingStructureSheafMap (fst g)) ≫
        (ConormalAlgebra.commRingPushforwardCompIso (fst g) g).hom.app
          (commRingStructureSheaf (relation g)) ≫
        eqToHom
          (congrArg
            (fun p ↦
              (commRingPushforward p).obj (commRingStructureSheaf (relation g)))
            (pullback.condition : fst g ≫ g = snd g ≫ g)) :=
  rfl

/-- `algebraMapSnd` is the pushforward of `snd^♯` followed by the composition
iso. -/
theorem algebraMapSnd_eq (g : Y ⟶ X) [Proper g] :
    algebraMapSnd g =
      (commRingPushforward g).map (commRingStructureSheafMap (snd g)) ≫
        (ConormalAlgebra.commRingPushforwardCompIso (snd g) g).hom.app
          (commRingStructureSheaf (relation g)) :=
  rfl

/-- The pointwise equalizer of the two kernel-pair algebra maps, as a
commutative-ring presheaf on the small étale site of `X`. -/
def equalizerPresheaf (g : Y ⟶ X) [Proper g] :
    (smallEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u} where
  obj U := equalizer ((algebraMapFst g).hom.app U) ((algebraMapSnd g).hom.app U)
  map {U V} iUV :=
    equalizer.lift
      (equalizer.ι ((algebraMapFst g).hom.app U) ((algebraMapSnd g).hom.app U) ≫
        (pushforwardStructureQcAlgebra g).obj.right.obj.map iUV)
      sorry
  map_id := sorry
  map_comp := sorry

/-- The underlying functor of `equalizerPresheaf` evaluates to the pointwise
equalizer of the kernel-pair algebra maps. -/
theorem equalizerPresheaf_obj (g : Y ⟶ X) [Proper g] (U : (smallEtaleSite X)ᵒᵖ) :
    (equalizerPresheaf g).obj U =
      equalizer ((algebraMapFst g).hom.app U) ((algebraMapSnd g).hom.app U) :=
  rfl

/-- The equalizer of the kernel-pair algebra maps, as a sheaf of commutative
rings on the small étale site of `X`. -/
def equalizerSheaf (g : Y ⟶ X) [Proper g] :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} where
  obj := equalizerPresheaf g
  property := sorry

/-- The underlying presheaf of `equalizerSheaf` is `equalizerPresheaf`. -/
theorem equalizerSheaf_obj (g : Y ⟶ X) [Proper g] :
    (equalizerSheaf g).obj = equalizerPresheaf g :=
  rfl

/-- The structure map `𝒪_X ⟶` the kernel-pair equalizer sheaf. -/
def equalizerStructureMap (g : Y ⟶ X) [Proper g] :
    commRingStructureSheaf X ⟶ equalizerSheaf g :=
  InducedCategory.homMk
    { app := fun U ↦
        equalizer.lift ((commRingStructureSheafMap g).hom.app U) sorry
      naturality := sorry }

/-- The quasi-coherent `𝒪_X`-algebra `𝒜` equalizing the two kernel-pair algebra
maps of a proper morphism `g`. -/
def equalizerAlgebra (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g] :
    X.QcAlgebraUnder where
  obj := Under.mk (equalizerStructureMap g)
  property := sorry

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
  sorry

/-- The inclusion of the kernel-pair equalizer algebra into `g_* 𝒪_Y`. -/
def inclusion (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g] :
    equalizerAlgebra g ⟶ pushforwardStructureQcAlgebra g :=
  InducedCategory.homMk
    (Under.homMk
      (InducedCategory.homMk
        { app := fun U ↦
            equalizer.ι ((algebraMapFst g).hom.app U) ((algebraMapSnd g).hom.app U)
          naturality := sorry })
      sorry)

/-- On sections, `inclusion g` is the equalizer inclusion of the two kernel-pair
algebra maps. -/
theorem inclusion_app (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g]
    (U : (smallEtaleSite X)ᵒᵖ) :
    (InducedCategory.Hom.hom (inclusion g).hom.right).app U =
      equalizer.ι ((algebraMapFst g).hom.app U) ((algebraMapSnd g).hom.app U) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.KernelPairCoequalizer
