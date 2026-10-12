/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RelativeDiagonal

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/- Example 57.8.6 (1): for a separated scheme morphism, the relative diagonal is a closed
immersion. -/
@[stacks 0FYV]
#check (AlgebraicGeometry.Scheme.FourierMukai.relativeDiagonal_isClosedImmersion :
  ∀ {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f],
    IsClosedImmersion (Limits.pullback.diagonal f))

/- Example 57.8.6 (2): the relative diagonal kernel is the degree-zero derived pushforward of
the underived diagonal structure module. -/
@[stacks 0FYV]
#check (AlgebraicGeometry.Scheme.FourierMukai.relativeDiagonalKernel_isomorphic_singlePushforward :
  ∀ {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f],
    IsIsomorphic (relativeDiagonalKernel f)
      ((DerivedCategory.singleFunctor (Limits.pullback f f).toRingedSpace.Modules 0).obj
        (Scheme.Hom.pushforwardStructureModule (Limits.pullback.diagonal f))))

/- Example 57.8.6 (3): the relative diagonal kernel has quasicoherent cohomology. -/
@[stacks 0FYV]
#check (AlgebraicGeometry.Scheme.FourierMukai.relativeDiagonalKernel_quasicoherent :
  ∀ {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f],
    Scheme.ModuleDerived.quasicoherentProperty (Limits.pullback f f)
      (relativeDiagonalKernel f))

/- Example 57.8.6 (4): the underived diagonal structure module is quasicoherent. -/
@[stacks 0FYV]
#check (AlgebraicGeometry.Scheme.FourierMukai.relativeDiagonalModule_isQuasicoherent :
  ∀ {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f],
    (Scheme.Hom.pushforwardStructureModule (Limits.pullback.diagonal f)).IsQuasicoherent)

/- Example 57.8.6 (5): the underived diagonal structure module is of finite type. -/
@[stacks 0FYV]
#check (AlgebraicGeometry.Scheme.FourierMukai.relativeDiagonalModule_isFiniteType :
  ∀ {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f],
    (Scheme.Hom.pushforwardStructureModule (Limits.pullback.diagonal f)).IsFiniteType)

/- Example 57.8.6 (6): the diagonal structure module is flat over the first projection. -/
@[stacks 0FYV]
#check (AlgebraicGeometry.Scheme.FourierMukai.relativeDiagonalModule_flat_fst :
  ∀ {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f],
    SheafOfModules.IsFlatOver
      (Scheme.Hom.pushforwardStructureModule (Limits.pullback.diagonal f))
      (Limits.pullback.fst f f).toShHom)

/- Example 57.8.6 (7): the diagonal structure module is flat over the second projection. -/
@[stacks 0FYV]
#check (AlgebraicGeometry.Scheme.FourierMukai.relativeDiagonalModule_flat_snd :
  ∀ {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f],
    SheafOfModules.IsFlatOver
      (Scheme.Hom.pushforwardStructureModule (Limits.pullback.diagonal f))
      (Limits.pullback.snd f f).toShHom)

/- Example 57.8.6 (8): the Fourier--Mukai transform with the relative diagonal kernel is
naturally isomorphic to the identity functor. -/
@[stacks 0FYV]
#check (AlgebraicGeometry.Scheme.FourierMukai.relativeDiagonalFunctor_iso_id :
  ∀ {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f],
    IsIsomorphic (FourierMukai.functor f f (relativeDiagonalKernel f))
      (𝟭 (RingedSpace.ModuleDerived X.toRingedSpace)))

/- Example 57.8.6 (9): the Fourier--Mukai transform with the relative diagonal kernel is
objectwise isomorphic to the identity. -/
@[stacks 0FYV]
#check (AlgebraicGeometry.Scheme.FourierMukai.relativeDiagonalFunctor_obj_iso :
  ∀ {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    (M : RingedSpace.ModuleDerived X.toRingedSpace),
    IsIsomorphic ((FourierMukai.functor f f (relativeDiagonalKernel f)).obj M) M)

end AlgebraicGeometry.Scheme.FourierMukai
