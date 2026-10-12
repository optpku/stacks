/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SymmetricAlgebra.Multiplication.Sheafification
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Symmetric-algebra sheaves on ringed spaces

The ringed-space API is a thin specialization of the symmetric-algebra functor on an arbitrary
commutative ringed site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.SymmetricAlg

variable {X : RingedSpace.{u}}

/-- The symmetric algebra of the module of sections over an open set. -/
abbrev obj (F : X.Modules) (U : (TopologicalSpace.Opens X)ᵒᵖ) :
    ModuleCat (X.presheaf.obj U) :=
  PresheafOfModules.SymmetricAlgebra.obj X.presheaf F.val U

/-- The sectionwise symmetric-algebra presheaf underlying a module sheaf on `X`. -/
noncomputable abbrev presheaf (F : X.Modules) : X.PresheafModules :=
  SheafOfModules.RingedSite.SymmetricAlgebra.presheaf X.sheaf F

/-- The morphism of sectionwise symmetric-algebra presheaves induced by a module-sheaf
morphism. -/
noncomputable abbrev presheafMap {F G : X.Modules} (f : F ⟶ G) :
    presheaf F ⟶ presheaf G :=
  SheafOfModules.RingedSite.SymmetricAlgebra.presheafMap X.sheaf f

/-- The degree-one inclusion into the sectionwise symmetric-algebra presheaf. -/
noncomputable abbrev presheafι (F : X.Modules) : F.val ⟶ presheaf F :=
  SheafOfModules.RingedSite.SymmetricAlgebra.presheafι X.sheaf F

/-- The symmetric-algebra functor on module sheaves over a ringed space. -/
noncomputable def functor (X : RingedSpace.{u}) : X.Modules ⥤ X.Modules :=
  SheafOfModules.RingedSite.SymmetricAlgebra.functor X.sheaf

/-- The underlying module sheaf of the symmetric algebra of `F`. -/
@[stacks 01CF "symmetric algebra of a module sheaf"]
noncomputable abbrev sheaf {X : RingedSpace.{u}} (F : X.Modules) : X.Modules :=
  SheafOfModules.RingedSite.SymmetricAlgebra.sheaf X.sheaf F

/-- The morphism on symmetric-algebra sheaves induced by a module-sheaf morphism. -/
noncomputable abbrev map {X : RingedSpace.{u}} {F G : X.Modules} (f : F ⟶ G) :
    sheaf F ⟶ sheaf G :=
  SheafOfModules.RingedSite.SymmetricAlgebra.map X.sheaf f

/-- The multiplicative unit of a symmetric-algebra sheaf on a ringed space. -/
@[stacks 01CF "unit of a symmetric-algebra sheaf on a ringed space"]
noncomputable abbrev one {X : RingedSpace.{u}} (F : X.Modules) :
    𝟙_ X.Modules ⟶ sheaf F :=
  SheafOfModules.RingedSite.SymmetricAlgebra.one X.sheaf F

/-- Multiplication on a symmetric-algebra sheaf on a ringed space. -/
@[stacks 01CF "multiplication on a symmetric-algebra sheaf on a ringed space"]
noncomputable abbrev mul {X : RingedSpace.{u}} (F : X.Modules) :
    tensorObj (sheaf F) (sheaf F) ⟶ sheaf F :=
  SheafOfModules.RingedSite.SymmetricAlgebra.mul X.sheaf F

/-- On underlying presheaves, the symmetric-algebra sheaf map is the sheafification of the
sectionwise symmetric-algebra map. -/
theorem map_eq_sheafification {X : RingedSpace.{u}} {F G : X.Modules} (f : F ⟶ G) :
    map f = (moduleSheafification X).map (presheafMap f) := sorry

/-- The degree-one inclusion from a module sheaf to its symmetric-algebra sheaf. -/
noncomputable abbrev ι {X : RingedSpace.{u}} (F : X.Modules) : F ⟶ sheaf F :=
  SheafOfModules.RingedSite.SymmetricAlgebra.ι X.sheaf F

/-- The degree-one inclusions into symmetric-algebra sheaves are natural. -/
theorem ι_naturality {X : RingedSpace.{u}} {F G : X.Modules} (f : F ⟶ G) :
    f ≫ ι G = ι F ≫ map f := sorry

/-- The canonical degree-one inclusion into the symmetric-algebra functor on `X`. -/
noncomputable abbrev unit (X : RingedSpace.{u}) : 𝟭 X.Modules ⟶ functor X :=
  SheafOfModules.RingedSite.SymmetricAlgebra.unit X.sheaf

end AlgebraicGeometry.RingedSpace.SymmetricAlg

scoped[AlgebraicGeometry] notation3:max "Symm(" ℱ ")" =>
  AlgebraicGeometry.RingedSpace.SymmetricAlg.sheaf ℱ
