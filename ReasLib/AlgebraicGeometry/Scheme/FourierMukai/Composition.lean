/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.TorIndependence
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.FourierMukai

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/-- The derived convolution kernel associated to a triple fibre-product diagram and two kernels. -/
noncomputable def convolutionKernel
    {S X Y Z T : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    (p12 : T ⟶ Limits.pullback f g)
    (p23 : T ⟶ Limits.pullback g h)
    (p13 : T ⟶ Limits.pullback f h)
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)
    (K' : RingedSpace.ModuleDerived (Limits.pullback g h).toRingedSpace) :
    RingedSpace.ModuleDerived (Limits.pullback f h).toRingedSpace :=
  (RingedSpace.moduleDerivedPushforward p13.toShHom).obj
    ((DerivedTensor.Right.functor
      ((RingedSpace.modulePullbackDerived p23.toLRSHom.toShHom).obj K')).obj
      ((RingedSpace.modulePullbackDerived p12.toLRSHom.toShHom).obj K))

/-- The convolution of two kernels has quasicoherent cohomology when the middle structural
morphism is quasi-compact and quasi-separated. -/
theorem convolutionKernel_quasicoherent
    {S X Y Z T : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    [QuasiCompact g] [QuasiSeparated g]
    (p12 : T ⟶ Limits.pullback f g)
    (p23 : T ⟶ Limits.pullback g h)
    (p13 : T ⟶ Limits.pullback f h)
    (hT : IsPullback p12 p23 (Limits.pullback.snd f g) (Limits.pullback.fst g h))
    (h_p13_x : p13 ≫ Limits.pullback.fst f h = p12 ≫ Limits.pullback.fst f g)
    (h_p13_z : p13 ≫ Limits.pullback.snd f h = p23 ≫ Limits.pullback.snd g h)
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)
    (K' : RingedSpace.ModuleDerived (Limits.pullback g h).toRingedSpace)
    (hK : Scheme.ModuleDerived.quasicoherentProperty (Limits.pullback f g) K)
    (hK' : Scheme.ModuleDerived.quasicoherentProperty (Limits.pullback g h) K') :
    Scheme.ModuleDerived.quasicoherentProperty (Limits.pullback f h)
      (convolutionKernel f g h p12 p23 p13 K K') := sorry

/-- The quasicoherent derived object represented by a convolution kernel. -/
noncomputable def quasicoherentConvolutionKernel
    {S X Y Z T : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    [QuasiCompact g] [QuasiSeparated g]
    (p12 : T ⟶ Limits.pullback f g)
    (p23 : T ⟶ Limits.pullback g h)
    (p13 : T ⟶ Limits.pullback f h)
    (hT : IsPullback p12 p23 (Limits.pullback.snd f g) (Limits.pullback.fst g h))
    (h_p13_x : p13 ≫ Limits.pullback.fst f h = p12 ≫ Limits.pullback.fst f g)
    (h_p13_z : p13 ≫ Limits.pullback.snd f h = p23 ≫ Limits.pullback.snd g h)
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (K' : Scheme.DerivedQCoh (Limits.pullback g h)) :
    Scheme.DerivedQCoh (Limits.pullback f h) :=
  { obj := convolutionKernel f g h p12 p23 p13 K.obj K'.obj
    property := convolutionKernel_quasicoherent f g h p12 p23 p13 hT h_p13_x h_p13_z
      K.obj K'.obj K.property K'.property }

/-- Under quasi-compactness and quasi-separatedness, flatness of the middle structural
morphism, and Tor-independence of the outer schemes, composition of quasicoherent
Fourier--Mukai transforms is naturally isomorphic to the transform associated to the derived
convolution kernel. -/
theorem compositionIsoExists
    {S X Y Z T : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [QuasiCompact h] [QuasiSeparated h] [Flat g]
    (hTor : Scheme.TorIndependentOver (Over.mk f) (Over.mk h))
    (p12 : T ⟶ Limits.pullback f g)
    (p23 : T ⟶ Limits.pullback g h)
    (p13 : T ⟶ Limits.pullback f h)
    (hT : IsPullback p12 p23 (Limits.pullback.snd f g) (Limits.pullback.fst g h))
    (h_p13_x : p13 ≫ Limits.pullback.fst f h = p12 ≫ Limits.pullback.fst f g)
    (h_p13_z : p13 ≫ Limits.pullback.snd f h = p23 ≫ Limits.pullback.snd g h)
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (K' : Scheme.DerivedQCoh (Limits.pullback g h)) :
    Nonempty ((quasicoherent f g K ⋙ quasicoherent g h K') ≅
      quasicoherent f h
        (quasicoherentConvolutionKernel f g h p12 p23 p13 hT h_p13_x h_p13_z K K')) := sorry

end AlgebraicGeometry.Scheme.FourierMukai
