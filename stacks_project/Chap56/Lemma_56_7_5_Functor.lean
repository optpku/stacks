/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Linear
public import stacks_project.Chap52.Lemma_52_15_3_ProRealization
public import stacks_project.Chap56.Lemma_56_5_2
public import stacks_project.Chap56.Lemma_56_7_5_Kernel

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
variable (x : X ⟶ Spec (CommRingCat.of k)) (y : Y ⟶ Spec (CommRingCat.of k))

/-- The `k`-linear structure on ringed-space modules induced by a structure morphism
to `Spec (CommRingCat.of k)`. -/
@[implicit_reducible]
noncomputable def baseLinearRingedSpace (f : X ⟶ Spec (CommRingCat.of k)) :
    Linear k X.toRingedSpace.Modules :=
  Linear.ofRingMorphism
    ((RingedSpace.GlobalSections.centerHom X.toRingedSpace).comp
      (Scheme.Hom.globalSectionsMap f))

/-- The `k`-linear structure on coherent modules induced by a structure morphism
to `Spec (CommRingCat.of k)`. -/
@[implicit_reducible]
noncomputable def baseLinearCoh (f : X ⟶ Spec (CommRingCat.of k)) :
    Linear k (RingedSpace.Coh X.toRingedSpace) :=
  @CategoryTheory.Linear.fullSubcategory _ _ _ k _
    (baseLinearRingedSpace f) (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)

/-- The relative scalar structure on coherent modules is the full-subcategory
structure induced from ringed-space modules. -/
theorem baseLinearCoh_def (f : X ⟶ Spec (CommRingCat.of k)) :
    baseLinearCoh f =
      @CategoryTheory.Linear.fullSubcategory _ _ _ k _
        (baseLinearRingedSpace f)
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) := sorry

/-- A functor of coherent modules is linear over chosen maps to the same affine
base when it is additive and linear for the scalar structures induced by those
maps. -/
class LinearOverCoh (F : RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace) :
    Prop
    extends F.Additive,
      @Functor.Linear k _ (RingedSpace.Coh X.toRingedSpace)
        (RingedSpace.Coh Y.toRingedSpace) _ _ _ _ (baseLinearCoh x) (baseLinearCoh y) F

/-- Relative coherence-linearity consists exactly of additivity and linearity for
the two base-induced scalar structures. -/
theorem linearOverCoh_iff
    (F : RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace) :
    LinearOverCoh x y F ↔
      F.Additive ∧
        @Functor.Linear k _ (RingedSpace.Coh X.toRingedSpace)
          (RingedSpace.Coh Y.toRingedSpace) _ _ _ _
            (baseLinearCoh x) (baseLinearCoh y) F := sorry

/-- The identity functor on coherent modules is linear over a fixed affine-base
structure morphism. -/
instance instLinearOverCoh_id : LinearOverCoh x x (𝟭 (RingedSpace.Coh X.toRingedSpace)) :=
  sorry

/-- A `k`-linear functor of coherent modules is exact-linear when it is an exact
functor `RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace`. -/
class ExactLinearOverCoh
    (F : RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace) : Prop
    extends LinearOverCoh x y F where
  exact :
    exactFunctor (RingedSpace.Coh X.toRingedSpace) (RingedSpace.Coh Y.toRingedSpace) F

/-- Exact-linearity on coherent modules is equivalent to relative `k`-linearity
together with exactness. -/
theorem exactLinearOverCoh_iff
    (F : RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace) :
    ExactLinearOverCoh x y F ↔
      LinearOverCoh x y F ∧
        exactFunctor (RingedSpace.Coh X.toRingedSpace)
          (RingedSpace.Coh Y.toRingedSpace) F := sorry

/-- The category of `k`-linear exact functors of coherent modules. -/
abbrev ExactLinearCohFunctor :=
  ObjectProperty.FullSubcategory fun F : RingedSpace.Coh X.toRingedSpace ⥤
    RingedSpace.Coh Y.toRingedSpace ↦ ExactLinearOverCoh x y F

/-- Objects of `ExactLinearCohFunctor` are exact `k`-linear functors of coherent
modules. -/
theorem exactLinearCohFunctor_property (F : ExactLinearCohFunctor x y) :
    ExactLinearOverCoh x y F.obj :=
  F.property

variable [IsNoetherian X]
variable [QuasiCompact (Limits.pullback.snd x y)] [QuasiSeparated (Limits.pullback.snd x y)]

/-- The underlying ringed-space functor of the restriction of (56.5.1.1) to
coherent modules. -/
noncomputable def restrictFourierMukaiUnderlying (K : (Limits.pullback x y).Modules)
    [IsCoherentFourierMukaiKernel x y K] :
    RingedSpace.Coh X.toRingedSpace ⥤ Y.toRingedSpace.Modules :=
  coherentToQCoh X ⋙
    Scheme.QCoh.fourierMukai x y (IsCoherentFourierMukaiKernel.toQCoh x y K) ⋙
      Scheme.QCoh.inclusion Y ⋙ Scheme.Modules.toRingedSpace Y

/-- The restriction of (56.5.1.1) to coherent modules lands in coherent modules. -/
theorem restrictFourierMukaiUnderlying_obj_isCoherent
    (K : (Limits.pullback x y).Modules) [IsCoherentFourierMukaiKernel x y K]
    (F : RingedSpace.Coh X.toRingedSpace) :
    SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf
      ((restrictFourierMukaiUnderlying x y K).obj F) := sorry

/-- Restriction of the Fourier--Mukai functor (56.5.1.1) to coherent modules. -/
noncomputable def restrictFourierMukai (K : (Limits.pullback x y).Modules)
    [IsCoherentFourierMukaiKernel x y K] :
    RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace :=
  (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf).lift
    (restrictFourierMukaiUnderlying x y K)
    (fun F ↦ restrictFourierMukaiUnderlying_obj_isCoherent x y K F)

/-- The underlying object of `restrictFourierMukai` is obtained from the
quasicoherent Fourier--Mukai functor of (56.5.1.1). -/
theorem restrictFourierMukai_obj (K : (Limits.pullback x y).Modules)
    [IsCoherentFourierMukaiKernel x y K] (F : RingedSpace.Coh X.toRingedSpace) :
    ((restrictFourierMukai x y K).obj F).obj =
      (Scheme.Modules.toRingedSpace Y).obj
        ((Scheme.QCoh.inclusion Y).obj
          ((Scheme.QCoh.fourierMukai x y
              (IsCoherentFourierMukaiKernel.toQCoh x y K)).obj
            ((coherentToQCoh X).obj F))) := sorry

/-- Restriction of (56.5.1.1) to coherent modules is `k`-linear. -/
instance instLinearOverCoh_restrictFourierMukai (K : (Limits.pullback x y).Modules)
    [IsCoherentFourierMukaiKernel x y K] :
    LinearOverCoh x y (restrictFourierMukai x y K) := sorry

/-- Restriction of (56.5.1.1) to coherent modules is exact. -/
instance instExactLinearOverCoh_restrictFourierMukai (K : (Limits.pullback x y).Modules)
    [IsCoherentFourierMukaiKernel x y K] :
    ExactLinearOverCoh x y (restrictFourierMukai x y K) := sorry

/-- A morphism of coherent Fourier--Mukai kernels induces a natural transformation
of the associated restricted Fourier--Mukai functors. -/
noncomputable def restrictFourierMukaiMap {K K' : (Limits.pullback x y).Modules}
    [IsCoherentFourierMukaiKernel x y K] [IsCoherentFourierMukaiKernel x y K']
    (α : K ⟶ K') :
    restrictFourierMukai x y K ⟶ restrictFourierMukai x y K' :=
  (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf).liftNatTrans
    (restrictFourierMukaiUnderlying_obj_isCoherent x y K)
    (restrictFourierMukaiUnderlying_obj_isCoherent x y K')
    (Functor.whiskerLeft (coherentToQCoh X)
      (Functor.whiskerRight
        (Functor.whiskerLeft (Scheme.QCoh.pullback (Limits.pullback.fst x y))
          (Functor.whiskerRight
            (Scheme.QCoh.tensorRightHom
              (homMk (P := Scheme.quasiCoherentModuleProperty (Limits.pullback x y)) α))
            (Scheme.QCoh.pushforward (Limits.pullback.snd x y))))
        (Scheme.QCoh.inclusion Y ⋙ Scheme.Modules.toRingedSpace Y)))

/-- The functor sending a coherent Fourier--Mukai kernel to the restriction of
(56.5.1.1) to coherent modules, viewed as a `k`-linear exact functor. -/
noncomputable def coherentExactFourierMukai :
    coherentFourierMukaiKernel x y ⥤ ExactLinearCohFunctor x y where
  obj K := ⟨restrictFourierMukai x y K.obj, inferInstance⟩
  map {K K'} α := homMk (restrictFourierMukaiMap x y α.hom)
  map_id := sorry
  map_comp := sorry

/-- The underlying functor of `coherentExactFourierMukai` is
`restrictFourierMukai`. -/
theorem coherentExactFourierMukai_obj (K : coherentFourierMukaiKernel x y) :
    ((coherentExactFourierMukai x y).obj K).obj = restrictFourierMukai x y K.obj :=
  sorry



end AlgebraicGeometry.Scheme
