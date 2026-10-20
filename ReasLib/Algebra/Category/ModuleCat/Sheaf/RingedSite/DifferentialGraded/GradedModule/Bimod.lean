module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Algebra.GradedMonoid
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.GradedModule
public import ReasLib.CategoryTheory.GradedObject.Monoidal.Colimit
public import ReasLib.CategoryTheory.Monoidal.Bimod.Module
import Mathlib.Tactic.CrossRefAttribute

/-!
# Graded modules as bimodule objects

The tensor-morphism presentation of a graded right module is canonically a bimodule from the
tensor-unit monoid to the underlying graded monoid of its algebra.  This bridge supplies the real
balanced tensor functor used to define relative graded flatness.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra

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

-- Local declaration justification (parser conflict): these lexical aliases keep bimodule formulas
-- readable without adding public notation beside the established graded-module `Mod(...)` scope.
local notation "ModO" => DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := 𝒪)
local notation "GrdO" => GradedObject ℤ ModO

namespace DifferentialGradedAlgebra.GradedModule

/-- Assemble a graded right-module action into a morphism of graded objects. -/
noncomputable def actionHom {A : DGA(𝒪)} (M : GradedModule A) :
    M.toGradedObject ⊗ A.toGradedObject ⟶ M.toGradedObject :=
  CategoryTheory.GradedObject.Monoidal.actionHom
    M.toGradedObject A.toGradedObject M.smul

/-- A graded right module as a bimodule over the tensor-unit monoid and its underlying graded
algebra. -/
@[stacks 0FSA "graded right module as a bimodule object"]
noncomputable def toBimod {A : DGA(𝒪)} (M : GradedModule A) :
    CategoryTheory.Bimod.RightModule A.toGradedMon where
  X := M.toGradedObject
  actLeft := (λ_ M.toGradedObject).hom
  actRight := actionHom M
  one_actLeft := sorry
  left_assoc := sorry
  actRight_one := sorry
  right_assoc := sorry
  middle_assoc := sorry

/-- A graded-module map as a morphism of the associated bimodule objects. -/
noncomputable def toBimodMap {A : DGA(𝒪)} {M N : GradedModule A} (f : M ⟶ N) :
    toBimod M ⟶ toBimod N where
  hom := f.hom
  left_act_hom := sorry
  right_act_hom := sorry

/-- The canonical functor from graded right modules to bimodule objects. -/
@[stacks 0FSA "graded right module bimodule functor"]
noncomputable def toBimodFunctor (A : DGA(𝒪)) :
    GradedModule A ⥤ CategoryTheory.Bimod.RightModule A.toGradedMon where
  obj := toBimod
  map := toBimodMap
  map_id := sorry
  map_comp := sorry

/-- The carrier of the associated bimodule is the original graded object. -/
@[simp]
theorem toBimod_X {A : DGA(𝒪)} (M : GradedModule A) :
    (toBimod M).X = M.obj := sorry

/-- The right action of the associated bimodule is the assembled graded action. -/
@[simp]
theorem toBimod_actRight {A : DGA(𝒪)} (M : GradedModule A) :
    (toBimod M).actRight = actionHom M := sorry

/-- The bimodule bridge sends a graded-module map to its degreewise underlying map. -/
@[simp]
theorem toBimodMap_hom {A : DGA(𝒪)} {M N : GradedModule A} (f : M ⟶ N) :
    (toBimodMap f).hom = f.hom := sorry

end DifferentialGradedAlgebra.GradedModule

namespace DifferentialGradedAlgebra

/-- Left modules over the underlying graded algebra of `A`. -/
@[stacks 0FSA "left graded module category"]
abbrev LeftGradedModule (A : DGA(𝒪)) :=
  CategoryTheory.Bimod.LeftModule A.toGradedMon

/-- Scoped notation for left modules over an underlying graded algebra. -/
scoped[SheafOfModules.RingedSite.LeftGradedModule] notation:max
    "LGrMod(" A:arg ")" =>
  _root_.SheafOfModules.RingedSite.DifferentialGradedAlgebra.LeftGradedModule A

end DifferentialGradedAlgebra

open scoped SheafOfModules.RingedSite.LeftGradedModule

namespace DifferentialGradedAlgebra.GradedModule

/-- Tensoring a fixed graded right `A`-module with graded left `A`-modules. -/
@[stacks 0FSA "relative graded tensor functor"]
noncomputable def tensorFunctor {A : DGA(𝒪)} (M : GradedModule A) :
    LGrMod(A) ⥤ GrdO :=
  CategoryTheory.Bimod.tensorFunctor (toBimod M)

/-- The relative tensor product of a graded right and a graded left `A`-module. -/
@[stacks 0FSA "relative graded tensor product"]
noncomputable abbrev tensor {A : DGA(𝒪)} (M : GradedModule A) (N : LGrMod(A)) : GrdO :=
  (tensorFunctor M).obj N

/-- A graded right `A`-module is flat when relative tensoring with it is exact. -/
@[stacks 0FSA "relative graded flatness"]
abbrev IsFlat {A : DGA(𝒪)} (M : GradedModule A) : Prop :=
  CategoryTheory.Bimod.IsFlat (toBimod M)

/-- Relatively flat graded right `A`-modules as an object property. -/
abbrev flatObjects (A : DGA(𝒪)) : ObjectProperty (GradedModule A) :=
  fun M ↦ IsFlat M

/-- Relative graded flatness is exactness of the balanced tensor functor. -/
theorem isFlat_iff {A : DGA(𝒪)} (M : GradedModule A) :
    IsFlat M ↔ exactFunctor LGrMod(A) GrdO (tensorFunctor M) := sorry

/-- Relative graded tensor is the underlying coequalizer-based balanced tensor product. -/
@[simp]
theorem tensor_eq {A : DGA(𝒪)} (M : GradedModule A) (N : LGrMod(A)) :
    tensor M N = ((toBimod M).tensorBimod N).X := sorry

end DifferentialGradedAlgebra.GradedModule

end

end SheafOfModules.RingedSite

end
