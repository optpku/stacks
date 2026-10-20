module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.FourierMukai
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RelativeDualizing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.StructureSheaf
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open RingedSpace.ModuleDerived.KFlat
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/-- The underlying dual Fourier--Mukai kernel
`(Y ×_S X → X ×_S Y)^*(K^∨ ⊗ Lpr₂^* ω^•_{Y/S})`. -/
noncomputable def dualKernelUnderlying
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a) :
    RingedSpace.ModuleDerived (Limits.pullback g f).toRingedSpace :=
  (RingedSpace.modulePullbackDerived
    (Limits.pullbackSymmetry g f).hom.toShHom).obj
      (MonoidalCategory.tensorObj
        ((MonoidalClosed.ihomOf H K.obj).obj
          (Scheme.DerivedQCoh.structureSheaf (Limits.pullback f g)).obj)
        ((Scheme.DerivedQCoh.pullback (Limits.pullback.snd f g)).obj
          (Scheme.DerivedQCoh.relativeDualizingComplex g a aAdjunction)).obj)

/-- A perfect kernel makes the underlying dual kernel quasicoherent. -/
theorem dualKernelUnderlying_quasicoherent
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a) :
    Scheme.ModuleDerived.quasicoherentProperty (Limits.pullback g f)
      (dualKernelUnderlying f g H K a aAdjunction) := sorry

/-- The dual Fourier--Mukai kernel `K'` on `Y ×_S X`. -/
noncomputable def dualKernel
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a) :
    Scheme.DerivedQCoh (Limits.pullback g f) :=
  ⟨dualKernelUnderlying f g H K a aAdjunction,
    dualKernelUnderlying_quasicoherent f g H K hK a aAdjunction⟩

/-- Forgetting quasicoherence identifies `dualKernel` with the explicit swap-pullback formula. -/
theorem dualKernel_obj
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a) :
    (dualKernel f g H K hK a aAdjunction).obj =
      dualKernelUnderlying f g H K a aAdjunction := rfl


/-- The Fourier--Mukai transform `Φ'` associated to the dual kernel `K'`. -/
noncomputable def dualTransform
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a) :
    Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh X :=
  quasicoherent g f (dualKernel f g H K hK a aAdjunction)

/-- The dual transform is the Fourier--Mukai transform associated to `dualKernel`. -/
theorem dualTransform_eq
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPerfect K.obj)
    (a : Scheme.DerivedQCoh S ⥤ Scheme.DerivedQCoh Y)
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a) :
    dualTransform f g H K hK a aAdjunction =
      quasicoherent g f (dualKernel f g H K hK a aAdjunction) := rfl


/-- Over a Noetherian base, for a finite type source and a flat proper Gorenstein target,
the Fourier--Mukai transform associated to the swapped dual of a perfect kernel, twisted
by the relative dualizing complex, admits the original transform as its right adjoint.
The resulting Hom equivalences are natural in both objects. -/
@[instance]
theorem dualTransform_nonempty_adjunction
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
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn g ⊣ a) :
    Nonempty (dualTransform f g H K hK a aAdjunction ⊣ quasicoherent f g K) := sorry

end AlgebraicGeometry.Scheme.FourierMukai
