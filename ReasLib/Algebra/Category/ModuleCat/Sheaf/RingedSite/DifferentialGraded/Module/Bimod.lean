/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Algebra.Monoid
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Colimit
public import ReasLib.CategoryTheory.Monoidal.Bimod.Module
import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential graded modules as bimodule objects

Right differential graded modules over a differential graded algebra are canonically bimodule
objects between the tensor-unit monoid and the algebra.  Left modules use the opposite orientation.
This realizes relative tensor products as Mathlib's coequalizer-based balanced tensor product.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable {𝒪 : Sheaf J CommRingCat.{w}}

namespace DifferentialGradedModule

/-- Assemble the homogeneous right action of a differential graded module into a morphism of
cochain complexes. -/
noncomputable def actionHom {𝒢 : DGA(𝒪)} (M : Mod(𝒢, d)) :
    HomologicalComplex.tensorObj M.toComplex 𝒢.toComplex ⟶ M.toComplex where
  f n := CategoryTheory.GradedObject.Monoidal.actionHom
    M.toComplex.X 𝒢.toComplex.X M.smul n
  comm' := sorry

/-- Extracting a homogeneous component of the assembled DG action recovers the original action
map. -/
@[simp]
theorem actionHom_component {𝒢 : DGA(𝒪)} (M : Mod(𝒢, d)) (n m : ℤ) :
    HomologicalComplex.Monoidal.tensorHomComponent (actionHom M) n m =
      M.smul n m := sorry

/-- A right differential graded module as a bimodule object from the tensor-unit monoid to its
differential graded algebra. -/
@[stacks 0FSA "right differential graded module as a bimodule object"]
noncomputable def toBimod {𝒢 : DGA(𝒪)} (M : Mod(𝒢, d)) :
    CategoryTheory.Bimod.RightModule 𝒢.toMon where
  X := M.toComplex
  actLeft := (λ_ M.toComplex).hom
  actRight := actionHom M
  one_actLeft := sorry
  left_assoc := sorry
  actRight_one := sorry
  right_assoc := sorry
  middle_assoc := sorry

/-- A differential graded module map as a morphism of the associated bimodule objects. -/
noncomputable def toBimodMap {𝒢 : DGA(𝒪)} {M N : Mod(𝒢, d)} (f : M ⟶ N) :
    toBimod M ⟶ toBimod N where
  hom := f.toCochainMap
  left_act_hom := sorry
  right_act_hom := sorry

/-- The canonical functor from right differential graded modules to bimodule objects. -/
@[stacks 0FSA "right differential graded module bimodule functor"]
noncomputable def toBimodFunctor (𝒢 : DGA(𝒪)) :
    Mod(𝒢, d) ⥤ CategoryTheory.Bimod.RightModule 𝒢.toMon where
  obj := toBimod
  map := toBimodMap
  map_id := sorry
  map_comp := sorry

/-- The underlying cochain complex of the bimodule associated to `M` is `M.toComplex`. -/
@[simp]
theorem toBimod_X {𝒢 : DGA(𝒪)} (M : Mod(𝒢, d)) :
    (toBimod M).X = M.toComplex := sorry

/-- The right action of the bimodule associated to `M` is its assembled DG action. -/
@[simp]
theorem toBimod_actRight {𝒢 : DGA(𝒪)} (M : Mod(𝒢, d)) :
    (toBimod M).actRight = actionHom M := sorry

/-- The bimodule bridge sends a DG-module map to its underlying cochain map. -/
@[simp]
theorem toBimodMap_hom {𝒢 : DGA(𝒪)} {M N : Mod(𝒢, d)} (f : M ⟶ N) :
    (toBimodMap f).hom = f.toCochainMap := sorry

end DifferentialGradedModule

namespace DifferentialGradedAlgebra

/-- The category of left differential graded modules over `𝒢`, realized as bimodule objects
from `𝒢` to the tensor-unit monoid. -/
@[stacks 0FSA "left differential graded module category"]
abbrev LeftModule (𝒢 : DGA(𝒪)) :=
  CategoryTheory.Bimod.LeftModule 𝒢.toMon

/-- Scoped notation for left differential graded modules. -/
scoped[SheafOfModules.RingedSite.LeftDifferentialGradedModule] notation:max
    "LMod(" 𝒢:arg ", " "d" ")" =>
  _root_.SheafOfModules.RingedSite.DifferentialGradedAlgebra.LeftModule 𝒢

end DifferentialGradedAlgebra

open scoped SheafOfModules.RingedSite.LeftDifferentialGradedModule

namespace DifferentialGradedModule

/-- Tensoring a fixed right DG `𝒢`-module with left DG `𝒢`-modules, using Mathlib's
balanced tensor product of bimodule objects. -/
@[stacks 0FSA "relative differential graded tensor functor"]
noncomputable def tensorFunctor {𝒢 : DGA(𝒪)} (M : Mod(𝒢, d)) :
    LMod(𝒢, d) ⥤
      CochainComplex (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := 𝒪)) ℤ :=
  CategoryTheory.Bimod.tensorFunctor (toBimod M)

/-- The relative tensor product of a right and a left differential graded `𝒢`-module. -/
@[stacks 0FSA "relative differential graded tensor product"]
noncomputable abbrev tensor {𝒢 : DGA(𝒪)} (M : Mod(𝒢, d)) (N : LMod(𝒢, d)) :
    CochainComplex (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := 𝒪)) ℤ :=
  (tensorFunctor M).obj N

/-- The relative tensor product is the underlying coequalizer-based balanced tensor product. -/
@[simp]
theorem tensor_eq {𝒢 : DGA(𝒪)} (M : Mod(𝒢, d)) (N : LMod(𝒢, d)) :
    tensor M N = ((toBimod M).tensorBimod N).X := sorry

end DifferentialGradedModule

end

end SheafOfModules.RingedSite

end
