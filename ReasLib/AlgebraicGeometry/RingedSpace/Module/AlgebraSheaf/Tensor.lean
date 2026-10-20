module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorAlgebra.Multiplication.Sheafification
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor-algebra sheaves on ringed spaces

The ringed-space API is a thin specialization of the tensor-algebra functor on an arbitrary
commutative ringed site.  The reusable sectionwise restriction maps, functoriality, and
degree-one inclusion are owned below the geometric layer.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.TensorAlg

variable {X : RingedSpace.{u}}

/-- The tensor algebra of the module of sections over an open set. -/
abbrev obj (F : X.Modules) (U : (TopologicalSpace.Opens X)ᵒᵖ) :
    ModuleCat (X.presheaf.obj U) :=
  PresheafOfModules.TensorAlgebra.obj X.presheaf F.val U

/-- The sectionwise tensor-algebra presheaf underlying a module sheaf on `X`. -/
noncomputable abbrev presheaf (F : X.Modules) : X.PresheafModules :=
  SheafOfModules.RingedSite.TensorAlgebra.presheaf X.sheaf F

/-- The morphism of sectionwise tensor-algebra presheaves induced by a module-sheaf
morphism. -/
noncomputable abbrev presheafMap {F G : X.Modules} (f : F ⟶ G) :
    presheaf F ⟶ presheaf G :=
  SheafOfModules.RingedSite.TensorAlgebra.presheafMap X.sheaf f

/-- The degree-one inclusion into the sectionwise tensor-algebra presheaf. -/
noncomputable abbrev presheafι (F : X.Modules) : F.val ⟶ presheaf F :=
  SheafOfModules.RingedSite.TensorAlgebra.presheafι X.sheaf F

/-- The tensor-algebra functor on module sheaves over a ringed space. -/
noncomputable def functor (X : RingedSpace.{u}) : X.Modules ⥤ X.Modules :=
  SheafOfModules.RingedSite.TensorAlgebra.functor X.sheaf

/-- Section 17.21 (01CF): the underlying module sheaf of the tensor algebra of `F`. -/
@[stacks 01CF "tensor algebra of a module sheaf"]
noncomputable abbrev sheaf {X : RingedSpace.{u}} (F : X.Modules) : X.Modules :=
  SheafOfModules.RingedSite.TensorAlgebra.sheaf X.sheaf F

/-- The morphism on tensor-algebra sheaves induced by a module-sheaf morphism. -/
noncomputable abbrev map {X : RingedSpace.{u}} {F G : X.Modules} (f : F ⟶ G) :
    sheaf F ⟶ sheaf G :=
  SheafOfModules.RingedSite.TensorAlgebra.map X.sheaf f

/-- The multiplicative unit of a tensor-algebra sheaf on a ringed space. -/
@[stacks 01CF "unit of a tensor-algebra sheaf on a ringed space"]
noncomputable abbrev one {X : RingedSpace.{u}} (F : X.Modules) :
    𝟙_ X.Modules ⟶ sheaf F :=
  SheafOfModules.RingedSite.TensorAlgebra.one X.sheaf F

/-- Multiplication on a tensor-algebra sheaf on a ringed space. -/
@[stacks 01CF "multiplication on a tensor-algebra sheaf on a ringed space"]
noncomputable abbrev mul {X : RingedSpace.{u}} (F : X.Modules) :
    tensorObj (sheaf F) (sheaf F) ⟶ sheaf F :=
  SheafOfModules.RingedSite.TensorAlgebra.mul X.sheaf F

/-- On underlying presheaves, the tensor-algebra sheaf map is the sheafification of the
sectionwise tensor-algebra map. -/
theorem map_eq_sheafification {X : RingedSpace.{u}} {F G : X.Modules} (f : F ⟶ G) :
    map f = (moduleSheafification X).map (presheafMap f) := sorry

/-- The degree-one inclusion from a module sheaf to its tensor-algebra sheaf. -/
noncomputable abbrev ι {X : RingedSpace.{u}} (F : X.Modules) : F ⟶ sheaf F :=
  SheafOfModules.RingedSite.TensorAlgebra.ι X.sheaf F

/-- The degree-one inclusions into tensor-algebra sheaves are natural. -/
theorem ι_naturality {X : RingedSpace.{u}} {F G : X.Modules} (f : F ⟶ G) :
    f ≫ ι G = ι F ≫ map f := sorry

/-- The canonical degree-one inclusion into the tensor-algebra functor on `X`. -/
noncomputable abbrev unit (X : RingedSpace.{u}) : 𝟭 X.Modules ⟶ functor X :=
  SheafOfModules.RingedSite.TensorAlgebra.unit X.sheaf

end AlgebraicGeometry.RingedSpace.TensorAlg

/- Textbook notation for the tensor-algebra module sheaf. -/
scoped[AlgebraicGeometry] notation3:max "T(" ℱ ")" =>
  AlgebraicGeometry.RingedSpace.TensorAlg.sheaf ℱ
