/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.ProRealization
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Linearity
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.FourierMukai.Kernel
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai.Naturality

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

section

variable [IsNoetherian X]
variable [QuasiCompact (Limits.pullback.snd x y)] [QuasiSeparated (Limits.pullback.snd x y)]

/-- The underlying ringed-space functor obtained by restricting the
quasicoherent Fourier--Mukai functor to coherent modules. -/
noncomputable def restrictFourierMukaiUnderlying (K : (Limits.pullback x y).Modules)
    [IsCoherentFourierMukaiKernel x y K] :
    RingedSpace.Coh X.toRingedSpace ⥤ Y.toRingedSpace.Modules :=
  coherentToQCoh X ⋙
    Scheme.QCoh.fourierMukai x y (IsCoherentFourierMukaiKernel.toQCoh x y K) ⋙
      Scheme.QCoh.inclusion Y ⋙ Scheme.Modules.toRingedSpace Y

/-- The Fourier--Mukai functor associated to a coherent kernel flat over the
source with support finite over the target sends coherent modules to coherent modules. -/
instance restrictFourierMukaiUnderlying_obj_isCoherent
    (K : (Limits.pullback x y).Modules) [IsCoherentFourierMukaiKernel x y K]
    (F : RingedSpace.Coh X.toRingedSpace) :
    SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf
      ((restrictFourierMukaiUnderlying x y K).obj F) := sorry

/-- The Fourier--Mukai functor restricted to coherent modules. -/
noncomputable def restrictFourierMukai (K : (Limits.pullback x y).Modules)
    [IsCoherentFourierMukaiKernel x y K] :
    RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace :=
  (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf).lift
    (restrictFourierMukaiUnderlying x y K)
    (fun F ↦ restrictFourierMukaiUnderlying_obj_isCoherent x y K F)

/-- The underlying object of `restrictFourierMukai` is obtained from the
quasicoherent Fourier--Mukai functor. -/
theorem restrictFourierMukai_obj (K : (Limits.pullback x y).Modules)
    [IsCoherentFourierMukaiKernel x y K] (F : RingedSpace.Coh X.toRingedSpace) :
    ((restrictFourierMukai x y K).obj F).obj =
      (Scheme.Modules.toRingedSpace Y).obj
        ((Scheme.QCoh.inclusion Y).obj
          ((Scheme.QCoh.fourierMukai x y
              (IsCoherentFourierMukaiKernel.toQCoh x y K)).obj
            ((coherentToQCoh X).obj F))) := sorry

/-- The Fourier--Mukai functor restricted to coherent modules is `k`-linear. -/
instance instLinearOverCoh_restrictFourierMukai (K : (Limits.pullback x y).Modules)
    [IsCoherentFourierMukaiKernel x y K] :
    LinearOverCoh x y (restrictFourierMukai x y K) := sorry

/-- The Fourier--Mukai functor restricted to coherent modules is exact. -/
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

/-- The natural transformation induced by the identity of a coherent kernel is
an identity. -/
theorem restrictFourierMukaiMap_id (K : (Limits.pullback x y).Modules)
    [IsCoherentFourierMukaiKernel x y K] :
    restrictFourierMukaiMap x y (𝟙 K) = 𝟙 (restrictFourierMukai x y K) := sorry

/-- The natural transformation induced by a composite of coherent kernel maps
is the composite of the induced natural transformations. -/
theorem restrictFourierMukaiMap_comp {K K' K'' : (Limits.pullback x y).Modules}
    [IsCoherentFourierMukaiKernel x y K] [IsCoherentFourierMukaiKernel x y K']
    [IsCoherentFourierMukaiKernel x y K''] (α : K ⟶ K') (β : K' ⟶ K'') :
    restrictFourierMukaiMap x y (α ≫ β) =
      restrictFourierMukaiMap x y α ≫ restrictFourierMukaiMap x y β := sorry

/-- The functor sending a coherent Fourier--Mukai kernel to its restricted
Fourier--Mukai functor, viewed as a `k`-linear exact functor. -/
noncomputable def coherentExactFourierMukai :
    coherentFourierMukaiKernel x y ⥤ ExactLinearCohFunctor x y where
  obj K := ⟨restrictFourierMukai x y K.obj, inferInstance⟩
  map {K K'} α := homMk (restrictFourierMukaiMap x y α.hom)
  map_id K := ObjectProperty.hom_ext _ (restrictFourierMukaiMap_id x y K.obj)
  map_comp α β := ObjectProperty.hom_ext _ (restrictFourierMukaiMap_comp x y α.hom β.hom)

/-- The underlying functor of `coherentExactFourierMukai` is
`restrictFourierMukai`. -/
theorem coherentExactFourierMukai_obj (K : coherentFourierMukaiKernel x y) :
    ((coherentExactFourierMukai x y).obj K).obj = restrictFourierMukai x y K.obj :=
  sorry

end

/-- For finite-type schemes over a field with separated source, the coherent
Fourier--Mukai assignment is an equivalence between coherent kernels flat over
the source with support finite over the target and exact linear functors on
coherent modules. -/
instance coherentExactFourierMukai_isEquivalence
    [x.FiniteType] [y.FiniteType] [IsSeparated x] [IsNoetherian X]
    [QuasiCompact (Limits.pullback.snd x y)] [QuasiSeparated (Limits.pullback.snd x y)] :
    (coherentExactFourierMukai x y).IsEquivalence := sorry

end AlgebraicGeometry.Scheme
