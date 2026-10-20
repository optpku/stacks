/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.LogPole
public import ReasLib.RingTheory.AdicCompletion.LocalMap
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RingedSpace.DeRham.LogPole.IsDefined

/-- If `S` is locally Noetherian, `f : X ⟶ S` is locally of finite type, `i : Y ⟶ X` is an
effective Cartier divisor, and the completed local-ring map
`AdicCompletion.mapLocal (i.stalkMap y).hom` is a split epimorphism for every `y : Y`, then the
relative de Rham complex with logarithmic poles along `i` is defined. -/
theorem of_completion_split {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [IsEffectiveCartierDivisor i]
    (h_section : ∀ y : Y,
      IsSplitEpi (CommRingCat.ofHom (AdicCompletion.mapLocal (i.stalkMap y).hom))) :
    IsDefined f i := sorry

end AlgebraicGeometry.RingedSpace.DeRham.LogPole.IsDefined
