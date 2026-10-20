/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Determinant.Prod
import Mathlib.Tactic.CrossRefAttribute

/-!
# Determinants of split short exact sequences on a ringed site

A splitting identifies the middle term with the biproduct of the two endpoints.  Consequently,
the determinant comparison morphism is explicit: apply the determinant biproduct morphism and
then transport along the inverse of the splitting isomorphism.  This file deliberately stops at
the split layer; constructing the comparison for an arbitrary short exact sequence requires a
separate local-splitting and descent API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.Determinant

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v})
variable {S : ShortComplex (ringedSiteModuleCategory J O)}

/-- The determinant comparison morphism determined by a splitting of a short complex of module
sheaves. -/
@[stacks 0B38 "determinant morphism from a splitting"]
noncomputable def splitHom (s : S.Splitting) :
    tensorObj (sheaf S.X₁) (sheaf S.X₃) ⟶ sheaf S.X₂ :=
  prodHom O S.X₁ S.X₃ ≫ (mapIso s.isoBinaryBiproduct.symm).hom

/-- After the determinant inclusion, the comparison attached to a splitting is the ambient
biproduct comparison transported to the middle term. -/
@[reassoc, stacks 0B38 "ambient determinant formula from a splitting"]
theorem splitHom_ι_prod (s : S.Splitting) :
    splitHom O s ≫ ι S.X₂ =
      prodAmbientHom O S.X₁ S.X₃ ≫
        ExteriorAlgebra.map O s.isoBinaryBiproduct.inv := sorry

/-- The ambient formula for a split determinant comparison uses the first map and the chosen
section into the middle term, followed by exterior multiplication. -/
@[reassoc, stacks 0B38 "maps and multiplication formula from a splitting"]
theorem splitHom_ι (s : S.Splitting) :
    splitHom O s ≫ ι S.X₂ =
      tensorHom (ι S.X₁) (ι S.X₃) ≫
        tensorHom (ExteriorAlgebra.map O S.f) (ExteriorAlgebra.map O s.s) ≫
          ExteriorAlgebra.mul O S.X₂ := sorry

/-- The determinant comparison constructed from a splitting is independent of the chosen
splitting. -/
@[stacks 0B38 "independence of the determinant morphism from a splitting"]
theorem splitHom_independent (s t : S.Splitting) :
    splitHom O s = splitHom O t := sorry

section IsIso

variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- The determinant comparison of a splitting is an isomorphism when both endpoint module
sheaves are finite locally free.  This records only the property and introduces no inverse data. -/
@[stacks 0B38 "split determinant morphism is an isomorphism"]
instance splitHom_isIso (s : S.Splitting)
    [SheafOfModules.IsFiniteLocallyFree S.X₁]
    [SheafOfModules.IsFiniteLocallyFree S.X₃] :
    IsIso (splitHom O s) := sorry

end IsIso

end SheafOfModules.RingedSite.Determinant
