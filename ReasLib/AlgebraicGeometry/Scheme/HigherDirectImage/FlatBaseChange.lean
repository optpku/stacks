/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flat Base Change for Higher Direct Images

This module records flat base-change comparisons for higher direct images of quasi-coherent
module sheaves along quasi-compact and quasi-separated scheme morphisms.
-/

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom
open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- In a cartesian square of schemes with flat base morphism, pullback of a higher direct image
of a quasicoherent module is isomorphic to the higher direct image of its pullback when the
original morphism is quasi-compact and quasi-separated. -/
theorem flatBaseChange_pullback_higherDirectImage_isomorphic
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g) [Flat g] [QuasiCompact f] [QuasiSeparated f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℕ) :
    IsIsomorphic
      ((Scheme.Modules.pullback g).obj
        (higherDirectImageModule f.toShHom ℱ i))
      (higherDirectImageModule f'.toShHom
        ((Scheme.Modules.pullback g').obj ℱ) i) := sorry

/-- In a cartesian square of schemes, tensoring the pullback of a higher direct image with a
quasi-coherent module flat over the original base identifies it with the higher direct image of
the tensor product of the two pulled-back modules. -/
theorem flatBaseChange_higherDirectImage_isomorphic
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g) [QuasiCompact f] [QuasiSeparated f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (𝒢 : S'.Modules) [𝒢.IsQuasicoherent]
    (hflat : Scheme.Modules.flatOver 𝒢 g) (i : ℕ) :
    IsIsomorphic
      (𝒢 ⊗ (Scheme.Modules.pullback g).obj
        (higherDirectImageModule f.toShHom ℱ i))
      (higherDirectImageModule f'.toShHom
        (((Scheme.Modules.pullback f').obj 𝒢) ⊗
          ((Scheme.Modules.pullback g').obj ℱ)) i) := sorry

end AlgebraicGeometry.Scheme
