/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorAlgebra.Multiplication.Sheafification
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Exterior-algebra sheaves on ringed spaces

This file is the ringed-space specialization of the exterior-algebra owner for arbitrary
commutative ringed sites.  It preserves the established names and notation while delegating all
sectionwise data and functoriality to reusable lower layers.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ExteriorAlg

variable {X : RingedSpace.{u}}

/-- The objectwise exterior algebra on sections of a module sheaf. -/
abbrev obj (F : X.Modules) (U : (Opens X)ᵒᵖ) :
    ModuleCat (X.presheaf.obj U) :=
  PresheafOfModules.ExteriorAlgebra.obj X.presheaf F.val U

/-- The sectionwise exterior-algebra presheaf underlying a module sheaf. -/
noncomputable abbrev presheaf (F : X.Modules) : X.PresheafModules :=
  SheafOfModules.RingedSite.ExteriorAlgebra.presheaf X.sheaf F

/-- The morphism of exterior-algebra presheaves induced by a module-sheaf morphism. -/
noncomputable abbrev presheafMap {F G : X.Modules} (f : F ⟶ G) :
    presheaf F ⟶ presheaf G :=
  SheafOfModules.RingedSite.ExteriorAlgebra.presheafMap X.sheaf f

/-- The degree-one inclusion into the sectionwise exterior-algebra presheaf. -/
noncomputable abbrev presheafι (F : X.Modules) : F.val ⟶ presheaf F :=
  SheafOfModules.RingedSite.ExteriorAlgebra.presheafι X.sheaf F

/-- The exterior-algebra functor on module sheaves over a ringed space. -/
noncomputable def functor (X : RingedSpace.{u}) : X.Modules ⥤ X.Modules :=
  SheafOfModules.RingedSite.ExteriorAlgebra.functor X.sheaf

/-- The exterior-algebra module sheaf of `F` on a ringed space. -/
@[stacks 01CF "exterior algebra of a module sheaf"]
noncomputable abbrev sheaf (F : X.Modules) : X.Modules :=
  SheafOfModules.RingedSite.ExteriorAlgebra.sheaf X.sheaf F

/-- The morphism on exterior-algebra sheaves induced by a morphism of module sheaves. -/
noncomputable abbrev map {F G : X.Modules} (f : F ⟶ G) : sheaf F ⟶ sheaf G :=
  SheafOfModules.RingedSite.ExteriorAlgebra.map X.sheaf f

/-- The multiplicative unit of an exterior-algebra sheaf on a ringed space. -/
@[stacks 01CF "unit of an exterior-algebra sheaf on a ringed space"]
noncomputable abbrev one (F : X.Modules) : 𝟙_ X.Modules ⟶ sheaf F :=
  SheafOfModules.RingedSite.ExteriorAlgebra.one X.sheaf F

/-- Multiplication on an exterior-algebra sheaf on a ringed space. -/
@[stacks 01CF "multiplication on an exterior-algebra sheaf on a ringed space"]
noncomputable abbrev mul (F : X.Modules) :
    tensorObj (sheaf F) (sheaf F) ⟶ sheaf F :=
  SheafOfModules.RingedSite.ExteriorAlgebra.mul X.sheaf F

/-- On underlying presheaves, the exterior-algebra sheaf map is the sheafification of the
sectionwise exterior-algebra map. -/
theorem map_eq_sheafification {F G : X.Modules} (f : F ⟶ G) :
    map f = (moduleSheafification X).map (presheafMap f) := sorry

/-- The degree-one inclusion from a module sheaf to its exterior-algebra sheaf. -/
noncomputable abbrev ι (F : X.Modules) : F ⟶ sheaf F :=
  SheafOfModules.RingedSite.ExteriorAlgebra.ι X.sheaf F

/-- The degree-one inclusions into exterior-algebra sheaves are natural. -/
theorem ι_naturality {F G : X.Modules} (f : F ⟶ G) :
    f ≫ ι G = ι F ≫ map f := sorry

/-- The canonical degree-one inclusion into the exterior-algebra functor on `X`. -/
noncomputable abbrev unit (X : RingedSpace.{u}) :
    CategoryTheory.Functor.id X.Modules ⟶ functor X :=
  SheafOfModules.RingedSite.ExteriorAlgebra.unit X.sheaf

end AlgebraicGeometry.RingedSpace.ExteriorAlg

scoped[AlgebraicGeometry] notation3:max "Λ(" ℱ ")" =>
  AlgebraicGeometry.RingedSpace.ExteriorAlg.sheaf ℱ
