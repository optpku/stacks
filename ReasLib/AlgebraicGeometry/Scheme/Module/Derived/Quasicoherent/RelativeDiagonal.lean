/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatOver
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.FourierMukai
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.StructureSheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/-- The derived pushforward of the structure sheaf along the relative diagonal. -/
noncomputable def relativeDiagonalKernel
    {S X : Scheme.{u}} (f : X ⟶ S) :
    RingedSpace.ModuleDerived (Limits.pullback f f).toRingedSpace :=
  (RingedSpace.moduleDerivedPushforward
      (Limits.pullback.diagonal f).toShHom).obj
    (Scheme.DerivedQCoh.structureSheaf X).obj

/-- The relative diagonal of a separated scheme morphism is a closed immersion. -/
theorem relativeDiagonal_isClosedImmersion
    {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] :
    IsClosedImmersion (Limits.pullback.diagonal f) := sorry

/-- The relative diagonal kernel is the degree-zero derived pushforward of the diagonal
structure module. -/
theorem relativeDiagonalKernel_isomorphic_singlePushforward
    {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] :
    IsIsomorphic (relativeDiagonalKernel f)
      ((DerivedCategory.singleFunctor (Limits.pullback f f).toRingedSpace.Modules 0).obj
        (Scheme.Hom.pushforwardStructureModule (Limits.pullback.diagonal f))) := sorry

/-- The relative diagonal kernel has quasicoherent cohomology. -/
theorem relativeDiagonalKernel_quasicoherent
    {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] :
    Scheme.ModuleDerived.quasicoherentProperty (Limits.pullback f f)
      (relativeDiagonalKernel f) := sorry

/-- The underived relative diagonal structure module is quasicoherent. -/
theorem relativeDiagonalModule_isQuasicoherent
    {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] :
    (Scheme.Hom.pushforwardStructureModule (Limits.pullback.diagonal f)).IsQuasicoherent := sorry

/-- The underived relative diagonal structure module is of finite type. -/
theorem relativeDiagonalModule_isFiniteType
    {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] :
    (Scheme.Hom.pushforwardStructureModule (Limits.pullback.diagonal f)).IsFiniteType := sorry

/-- The relative diagonal structure module is flat over the first projection. -/
theorem relativeDiagonalModule_flat_fst
    {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] :
    SheafOfModules.IsFlatOver
      (Scheme.Hom.pushforwardStructureModule (Limits.pullback.diagonal f))
      (Limits.pullback.fst f f).toShHom := sorry

/-- The relative diagonal structure module is flat over the second projection. -/
theorem relativeDiagonalModule_flat_snd
    {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] :
    SheafOfModules.IsFlatOver
      (Scheme.Hom.pushforwardStructureModule (Limits.pullback.diagonal f))
      (Limits.pullback.snd f f).toShHom := sorry

/-- The Fourier--Mukai transform with the relative diagonal kernel is naturally isomorphic
to the identity functor. -/
theorem relativeDiagonalFunctor_iso_id
    {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] :
    IsIsomorphic (FourierMukai.functor f f (relativeDiagonalKernel f))
      (𝟭 (RingedSpace.ModuleDerived X.toRingedSpace)) := sorry

/-- The Fourier--Mukai transform with the relative diagonal kernel is objectwise isomorphic
to the identity. -/
theorem relativeDiagonalFunctor_obj_iso
    {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    (M : RingedSpace.ModuleDerived X.toRingedSpace) :
    IsIsomorphic ((FourierMukai.functor f f (relativeDiagonalKernel f)).obj M) M := sorry

end AlgebraicGeometry.Scheme.FourierMukai
