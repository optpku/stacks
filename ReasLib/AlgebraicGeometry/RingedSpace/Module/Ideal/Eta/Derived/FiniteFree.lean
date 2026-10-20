/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Stalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Eta.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Torsion.At
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.InvertiblePower.RankOne
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk.Tensor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-free cohomology stalks of the derived eta functor

The reusable core is the stalkwise form of the Berthelot-Ogus cohomology formula.  Pointwise
torsion freeness removes the torsion quotient, and a locally principal regular ideal makes the
remaining integral tensor power free of rank one at the chosen stalk.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite.IdealSheaf
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IdealSheaf.Eta.Derived

variable {X : RingedSpace.{u}}

/-- The derived form of the Berthelot-Ogus cohomology formula: degree-`i` cohomology of `Lη_I M`
is the `i`th tensor power of `I` tensored with the quotient of `H^i(M)` by its `I`-torsion. -/
@[stacks 0F8N "derived cohomology formula"]
theorem tensorPower_torsionQuotient_isomorphic_cohomology
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)] (M : ModuleDerived X) (i : ℤ) :
    IsIsomorphic
      (((I : X.Modules) ^⊗ i) ⊗
        torsionQuotient (O := X.sheaf) I (M.cohomologySheaf i))
      (ModuleDerived.cohomologySheaf ((functor I).obj M) i) := sorry

/-- If `H^i(M)` is `I`-torsion-free at `x`, then the cohomology stalk of `Lη_I M` is the tensor
product of `H^i(M)_x` with the stalk of `I^⊗ i`. -/
@[stacks 0GTA "stalkwise tensor-power formula"]
theorem cohomologyStalk_isomorphic_tensorPower
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)] (M : ModuleDerived X) (i : ℤ) (x : X)
    (hM : IsTorsionFreeAt I (M.cohomologySheaf i) x) :
    IsIsomorphic
      (stalkModuleCat ((I : X.Modules) ^⊗ i) x ⊗ M.cohomologyStalk i x)
      (ModuleDerived.cohomologyStalk ((functor I).obj M) i x) := sorry

/-- For a locally principal regular ideal and a finite-free input cohomology stalk, the output
cohomology stalk is isomorphic to the input stalk.  This is the structural form of Lemma 20.55.10
from which finite freeness and rank equality follow. -/
@[stacks 0GTA "structural stalk form"]
theorem cohomologyStalk_isomorphic
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [IsRegularPrincipal I] (M : ModuleDerived X) (i : ℤ) (x : X)
    (hM : M.cohomologyStalkFiniteFree i x) :
    IsIsomorphic
      (ModuleDerived.cohomologyStalk ((functor I).obj M) i x)
      (M.cohomologyStalk i x) := sorry

/-- Lemma 20.55.10 (0GTA) (1): finite freeness of a cohomology stalk is preserved by the
derived eta functor for a locally principal regular ideal.  The nonzero-stalk assumption is not
needed for this clause. -/
@[stacks 0GTA "(1)"]
theorem cohomologyStalkFiniteFree
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [IsRegularPrincipal I] (M : ModuleDerived X) (i : ℤ) (x : X)
    (hM : M.cohomologyStalkFiniteFree i x) :
    ModuleDerived.cohomologyStalkFiniteFree ((functor I).obj M) i x := sorry

/-- Lemma 20.55.10 (0GTA) (2): over a nonzero stalk ring, the derived eta functor preserves the
rank of a finite-free cohomology stalk. -/
@[stacks 0GTA "(2)"]
theorem cohomologyStalk_rank_eq
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [IsRegularPrincipal I] (M : ModuleDerived X) (i : ℤ) (x : X)
    [Nontrivial (X.presheaf.stalk x)]
    (hM : M.cohomologyStalkFiniteFree i x) :
    Module.rank (X.presheaf.stalk x)
        (ModuleDerived.cohomologyStalk ((functor I).obj M) i x) =
      Module.rank (X.presheaf.stalk x) (M.cohomologyStalk i x) := sorry

/-- The finite-rank form of Lemma 20.55.10, convenient for downstream dimension calculations. -/
@[stacks 0GTA "finite-rank form"]
theorem cohomologyStalk_finrank_eq
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [IsRegularPrincipal I] (M : ModuleDerived X) (i : ℤ) (x : X)
    [Nontrivial (X.presheaf.stalk x)]
    (hM : M.cohomologyStalkFiniteFree i x) :
    Module.finrank (X.presheaf.stalk x)
        (ModuleDerived.cohomologyStalk ((functor I).obj M) i x) =
      Module.finrank (X.presheaf.stalk x) (M.cohomologyStalk i x) := sorry

end AlgebraicGeometry.RingedSpace.IdealSheaf.Eta.Derived
