module

public import stacks_project.Chap57.Lemma_57_8_8_Comparison
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpace.ModuleDerived.KFlat
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/-- Lemma 57.8.8: over a Noetherian scheme `S`, if `Y ⟶ S` is flat proper Gorenstein and
`X ⟶ S` is of finite type, a Fourier--Mukai functor `Φ` with perfect kernel `K` has dual
kernel `K' = swap^*(K^∨ ⊗ Lpr₂^* ω^•_{Y/S})`, and the associated transform `Φ'` satisfies a
canonical functorial isomorphism `Hom_Y(N, Φ(M)) ≅ Hom_X(Φ'(N), M)`. -/
@[stacks 0FYX]
theorem dualHomComparison_bijective
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S]
    [IsProper g] [Flat g] [AlgebraicGeometry.Gorenstein g]
    [LocallyOfFiniteType f]
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HomotopyTensorDescends (Limits.pullback g f).toRingedSpace]
    [TensorDescends (Limits.pullback g f).toRingedSpace]
    [IsLocalization (Limits.pullback g f).toRingedSpace]
    [HomotopyTensorDescends (Limits.pullback f g).toRingedSpace]
    [TensorDescends (Limits.pullback f g).toRingedSpace]
    [IsLocalization (Limits.pullback f g).toRingedSpace]
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.fst f g).toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullback.fst f g).toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullbackSymmetry g f).hom.toShHom)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    [CompactSpace (Limits.pullback f g : Scheme.{u})]
    [QuasiSeparatedSpace (Limits.pullback f g : Scheme.{u})]
    [CompactSpace (Limits.pullback g f : Scheme.{u})]
    [QuasiSeparatedSpace (Limits.pullback g f : Scheme.{u})]
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a)
    (M : Scheme.DerivedQCoh X) (N : Scheme.DerivedQCoh Y) :
    Function.Bijective (dualHomComparison f g H K hK a aAdjunction M N) := sorry

/-- The dual Hom comparison is natural in the source object `N`. -/
theorem dualHomComparison_naturality_left
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HomotopyTensorDescends (Limits.pullback g f).toRingedSpace]
    [TensorDescends (Limits.pullback g f).toRingedSpace]
    [IsLocalization (Limits.pullback g f).toRingedSpace]
    [HomotopyTensorDescends (Limits.pullback f g).toRingedSpace]
    [TensorDescends (Limits.pullback f g).toRingedSpace]
    [IsLocalization (Limits.pullback f g).toRingedSpace]
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.fst f g).toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullback.fst f g).toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullbackSymmetry g f).hom.toShHom)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    [CompactSpace (Limits.pullback f g : Scheme.{u})]
    [QuasiSeparatedSpace (Limits.pullback f g : Scheme.{u})]
    [CompactSpace (Limits.pullback g f : Scheme.{u})]
    [QuasiSeparatedSpace (Limits.pullback g f : Scheme.{u})]
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a)
    {N N' : Scheme.DerivedQCoh Y} (k : N ⟶ N')
    (M : Scheme.DerivedQCoh X)
    (phi : N' ⟶ (quasicoherent f g K).obj M) :
    dualHomComparison f g H K hK a aAdjunction M N (k ≫ phi) =
      (dualTransform f g H K hK a aAdjunction).map k ≫
        dualHomComparison f g H K hK a aAdjunction M N' phi := sorry

/-- The dual Hom comparison is natural in the target object `M`. -/
theorem dualHomComparison_naturality_right
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HomotopyTensorDescends (Limits.pullback g f).toRingedSpace]
    [TensorDescends (Limits.pullback g f).toRingedSpace]
    [IsLocalization (Limits.pullback g f).toRingedSpace]
    [HomotopyTensorDescends (Limits.pullback f g).toRingedSpace]
    [TensorDescends (Limits.pullback f g).toRingedSpace]
    [IsLocalization (Limits.pullback f g).toRingedSpace]
    [HomotopyTensorDescends X.toRingedSpace]
    [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom (Limits.pullback.fst f g).toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullback.fst f g).toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullbackSymmetry g f).hom.toShHom)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    [CompactSpace (Limits.pullback f g : Scheme.{u})]
    [QuasiSeparatedSpace (Limits.pullback f g : Scheme.{u})]
    [CompactSpace (Limits.pullback g f : Scheme.{u})]
    [QuasiSeparatedSpace (Limits.pullback g f : Scheme.{u})]
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a)
    (N : Scheme.DerivedQCoh Y)
    {M M' : Scheme.DerivedQCoh X} (k : M ⟶ M')
    (phi : N ⟶ (quasicoherent f g K).obj M) :
    dualHomComparison f g H K hK a aAdjunction M' N
        (phi ≫ (quasicoherent f g K).map k) =
      dualHomComparison f g H K hK a aAdjunction M N phi ≫ k := sorry

end AlgebraicGeometry.Scheme.FourierMukai
