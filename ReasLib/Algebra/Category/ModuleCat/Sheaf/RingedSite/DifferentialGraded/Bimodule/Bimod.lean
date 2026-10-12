/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Bimodule
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Bimod
public import ReasLib.CategoryTheory.GradedObject.Monoidal.Action
import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential graded bimodule sheaves as bimodule objects

A differential graded `(A, B)`-bimodule sheaf canonically determines a bimodule object between
the monoid objects associated to `A` and `B` in the category of cochain complexes.  This is the
common bridge through which relative tensor products and relative internal Homs reuse Mathlib's
generic bimodule API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule
open scoped SheafOfModules.RingedSite.DifferentialGradedBimodule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedBimodule

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- Assemble the homogeneous left action of a differential graded bimodule into a morphism of
cochain complexes. -/
@[stacks 0FRS "differential graded bimodule left action"]
noncomputable def leftActionHom {𝒜 𝒝 : DGA(𝒪)} (N : Mod(𝒜, 𝒝, d)) :
    HomologicalComplex.tensorObj 𝒜.toComplex N.toComplex ⟶ N.toComplex where
  f n := CategoryTheory.GradedObject.Monoidal.leftActionHom
    𝒜.toComplex.X N.toComplex.X N.leftMul n
  comm' := sorry

/-- Extracting a homogeneous component of the assembled left action recovers the original
degreewise left action. -/
@[simp]
theorem leftActionHom_component {𝒜 𝒝 : DGA(𝒪)} (N : Mod(𝒜, 𝒝, d)) (n m : ℤ) :
    HomologicalComplex.Monoidal.tensorHomComponent (leftActionHom N) n m =
      N.leftMul n m := sorry

/-- A differential graded `(A, B)`-bimodule sheaf as a bimodule object between the associated
cochain-complex monoids. -/
@[stacks 0FRS "differential graded bimodule as a bimodule object"]
noncomputable def toBimod {𝒜 𝒝 : DGA(𝒪)} (N : Mod(𝒜, 𝒝, d)) :
    Bimod 𝒜.toMon 𝒝.toMon where
  X := N.toComplex
  actLeft := leftActionHom N
  actRight := DifferentialGradedModule.actionHom N.toRightModule
  one_actLeft := sorry
  left_assoc := sorry
  actRight_one := sorry
  right_assoc := sorry
  middle_assoc := sorry

/-- A differential graded bimodule map as a morphism between the associated bimodule objects. -/
noncomputable def toBimodMap {𝒜 𝒝 : DGA(𝒪)} {N N' : Mod(𝒜, 𝒝, d)} (f : N ⟶ N') :
    toBimod N ⟶ toBimod N' where
  hom := f.toRightHom.toCochainMap
  left_act_hom := sorry
  right_act_hom := sorry

/-- The canonical functor from differential graded bimodule sheaves to bimodule objects. -/
@[stacks 0FRS "differential graded bimodule object functor"]
noncomputable def toBimodFunctor (𝒜 𝒝 : DGA(𝒪)) :
    Mod(𝒜, 𝒝, d) ⥤ Bimod 𝒜.toMon 𝒝.toMon where
  obj := toBimod
  map := toBimodMap
  map_id := sorry
  map_comp := sorry

/-- The underlying cochain complex of the bimodule object associated to `N` is `N.toComplex`. -/
@[simp]
theorem toBimod_X {𝒜 𝒝 : DGA(𝒪)} (N : Mod(𝒜, 𝒝, d)) :
    (toBimod N).X = N.toComplex := sorry

/-- The assembled left action is the left action of the associated bimodule object. -/
@[simp]
theorem toBimod_actLeft {𝒜 𝒝 : DGA(𝒪)} (N : Mod(𝒜, 𝒝, d)) :
    (toBimod N).actLeft = leftActionHom N := sorry

/-- The assembled right action is the right action of the associated bimodule object. -/
@[simp]
theorem toBimod_actRight {𝒜 𝒝 : DGA(𝒪)} (N : Mod(𝒜, 𝒝, d)) :
    (toBimod N).actRight = DifferentialGradedModule.actionHom N.toRightModule := sorry

/-- The bimodule-object bridge sends a DG bimodule map to its underlying cochain map. -/
@[simp]
theorem toBimodMap_hom {𝒜 𝒝 : DGA(𝒪)} {N N' : Mod(𝒜, 𝒝, d)}
    (f : N ⟶ N') :
    (toBimodMap f).hom = f.toRightHom.toCochainMap := sorry

end

end SheafOfModules.RingedSite.DifferentialGradedBimodule

end
