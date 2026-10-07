module

public import stacks_project.Chap57.Lemma_57_8_9_Perfect
public import stacks_project.Chap57.Lemma_57_8_9_DualKernel
public import stacks_project.Chap57.Lemma_57_8_3
public import stacks_project.Chap57.Lemma_57_8_8_DualKernel
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein
public import ReasLib.AlgebraicGeometry.Scheme.TorIndependence
@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/-- Lemma 57.8.9 (1): if `S` is Noetherian and `X`, `Y` are proper and flat over `S`,
a perfect kernel on `X ×_S Y` induces a Fourier--Mukai functor
`Φ_K : D_perf(𝒪_X) ⟶ D_perf(𝒪_Y)`. -/
@[stacks 0FYY]
abbrev fourierMukaiPerfect {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S] [IsProper f] [Flat f] [IsProper g] [Flat g]
    (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback f g).toRingedSpace) :
    @RingedSpace.ModuleDerived.Perfect X.toRingedSpace ⥤
      @RingedSpace.ModuleDerived.Perfect Y.toRingedSpace :=
  perfectNoetherian f g K

/-- The source-facing restricted Fourier--Mukai functor is the Noetherian
perfect restriction of `functor`. -/
theorem fourierMukaiPerfect_eq {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S] [IsProper f] [Flat f] [IsProper g] [Flat g]
    (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback f g).toRingedSpace) :
    fourierMukaiPerfect f g K = perfectNoetherian f g K := sorry

/-- The convolution kernel of two perfect kernels remains perfect. -/
theorem convolutionKernel_isPerfect
    {S X Y Z T : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    [IsNoetherian S]
    [IsProper f] [Flat f] [IsProper g] [Flat g] [IsProper h] [Flat h]
    (p12 : T ⟶ Limits.pullback f g)
    (p23 : T ⟶ Limits.pullback g h)
    (p13 : T ⟶ Limits.pullback f h)
    (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback f g).toRingedSpace)
    (K' : @RingedSpace.ModuleDerived.Perfect (Limits.pullback g h).toRingedSpace) :
    RingedSpace.ModuleDerived.IsPerfect
      (convolutionKernel f g h p12 p23 p13 K.obj K'.obj) := sorry

/-- Lemma 57.8.9 (2): for `X`, `Y`, `Z` proper and flat over a Noetherian scheme `S`,
the composition of the restricted Fourier--Mukai functors of two perfect kernels
equals the restricted transform of the Lemma 57.8.3 convolution kernel. -/
@[stacks 0FYY]
theorem perfect_composition_eq_convolution
    {S X Y Z T : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    [IsNoetherian S]
    [IsProper f] [Flat f] [IsProper g] [Flat g] [IsProper h] [Flat h]
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [QuasiCompact h] [QuasiSeparated h]
    (hTor : Scheme.TorIndependentOver (Over.mk f) (Over.mk h))
    (p12 : T ⟶ Limits.pullback f g)
    (p23 : T ⟶ Limits.pullback g h)
    (p13 : T ⟶ Limits.pullback f h)
    (hT : IsPullback p12 p23 (Limits.pullback.snd f g) (Limits.pullback.fst g h))
    (h_p13_x : p13 ≫ Limits.pullback.fst f h = p12 ≫ Limits.pullback.fst f g)
    (h_p13_z : p13 ≫ Limits.pullback.snd f h = p23 ≫ Limits.pullback.snd g h)
    (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback f g).toRingedSpace)
    (K' : @RingedSpace.ModuleDerived.Perfect (Limits.pullback g h).toRingedSpace)
    (K'' : @RingedSpace.ModuleDerived.Perfect (Limits.pullback f h).toRingedSpace)
    (hK'' : K''.obj = convolutionKernel f g h p12 p23 p13 K.obj K'.obj) :
    perfectNoetherian f g K ⋙ perfectNoetherian g h K' =
      perfectNoetherian f h K'' := sorry

/-- Lemma 57.8.9 (3): if in addition `X ⟶ S` is Gorenstein, then the Fourier--Mukai
functor of the swap-pullback of `Lpr₁^* ω_{X/S}^• ⊗^L K^∨` is a right adjoint of
`Φ_K` on perfect complexes. -/
@[stacks 0FYY, instance]
instance instIsRightAdjoint_perfectNoetherian_dualKernelOfPr1
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S] [IsProper f] [IsProper g] [Flat g]
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [AlgebraicGeometry.Gorenstein f]
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback f g).toRingedSpace)
    (hK : Scheme.ModuleDerived.quasicoherentProperty (Limits.pullback f g) K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh X)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a) :
    (perfectNoetherian g f
        ⟨(dualKernelOfPr1 f g H ⟨K.obj, hK⟩ K.property a aAdjunction).obj,
          dualKernelOfPr1_isPerfect f g H ⟨K.obj, hK⟩ K.property a aAdjunction⟩).IsRightAdjoint :=
  sorry

/-- The left adjoint recovered from the Gorenstein source dual kernel is `Φ_K`. -/
theorem leftAdjoint_eq_perfectNoetherian
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S] [IsProper f] [IsProper g] [Flat g]
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [AlgebraicGeometry.Gorenstein f]
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback f g).toRingedSpace)
    (hK : Scheme.ModuleDerived.quasicoherentProperty (Limits.pullback f g) K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh X)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a) :
    (Functor.leftAdjoint
        (perfectNoetherian g f
          ⟨(dualKernelOfPr1 f g H ⟨K.obj, hK⟩ K.property a aAdjunction).obj,
            dualKernelOfPr1_isPerfect f g H ⟨K.obj, hK⟩ K.property a aAdjunction⟩)) =
      perfectNoetherian f g K := sorry

/-- Lemma 57.8.9 (4): if in addition `Y ⟶ S` is Gorenstein, then the Fourier--Mukai
functor of the swap-pullback of `Lpr₂^* ω_{Y/S}^• ⊗^L K^∨` is a left adjoint of
`Φ_K` on perfect complexes. -/
@[stacks 0FYY, instance]
instance instIsLeftAdjoint_perfectNoetherian_dualKernel
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S] [IsProper f] [Flat f] [IsProper g]
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [AlgebraicGeometry.Gorenstein g]
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback f g).toRingedSpace)
    (hK : Scheme.ModuleDerived.quasicoherentProperty (Limits.pullback f g) K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a) :
    (perfectNoetherian g f
        ⟨(dualKernel f g H ⟨K.obj, hK⟩ K.property a aAdjunction).obj,
          dualKernel_isPerfect f g H ⟨K.obj, hK⟩ K.property a aAdjunction⟩).IsLeftAdjoint :=
  sorry

/-- The right adjoint recovered from the Gorenstein target dual kernel is `Φ_K`. -/
theorem rightAdjoint_eq_perfectNoetherian
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S] [IsProper f] [Flat f] [IsProper g]
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [AlgebraicGeometry.Gorenstein g]
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback f g).toRingedSpace)
    (hK : Scheme.ModuleDerived.quasicoherentProperty (Limits.pullback f g) K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a) :
    (Functor.rightAdjoint
        (perfectNoetherian g f
          ⟨(dualKernel f g H ⟨K.obj, hK⟩ K.property a aAdjunction).obj,
            dualKernel_isPerfect f g H ⟨K.obj, hK⟩ K.property a aAdjunction⟩)) =
      perfectNoetherian f g K := sorry

end AlgebraicGeometry.Scheme.FourierMukai
