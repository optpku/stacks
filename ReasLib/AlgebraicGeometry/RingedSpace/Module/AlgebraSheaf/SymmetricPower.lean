module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SymmetricPower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Symmetric powers of module sheaves on ringed spaces

The degree-`n` symmetric power of a module sheaf is obtained by taking sectionwise symmetric
powers of its underlying module presheaf and then sheafifying. The construction is exposed as a
degreewise functor. Multiplication, the graded algebra, and local properties live in focused
downstream modules.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.SymmetricPower

/-- The objectwise symmetric power of sections over an open of `X`. -/
@[stacks 01CG "objectwise symmetric power on a ringed space"]
abbrev obj {X : RingedSpace.{u}} (F : X.Modules) (n : ℕ)
    (U : (TopologicalSpace.Opens X)ᵒᵖ) : ModuleCat (X.presheaf.obj U) :=
  PresheafOfModules.SymmetricPower.obj X.presheaf F.val n U

/-- The sectionwise degree-`n` symmetric-power presheaf underlying a module sheaf on `X`. -/
@[stacks 01CG "sectionwise symmetric power on a ringed space"]
noncomputable abbrev presheaf {X : RingedSpace.{u}} (F : X.Modules) (n : ℕ) :
    X.PresheafModules :=
  SheafOfModules.RingedSite.SymmetricPower.presheaf X.sheaf F n

/-- Evaluation of the sectionwise symmetric-power presheaf at an open of `X`. -/
@[simp, stacks 01CG "objectwise symmetric power on a ringed space"]
theorem presheaf_obj {X : RingedSpace.{u}} (F : X.Modules) (n : ℕ)
    (U : (TopologicalSpace.Opens X)ᵒᵖ) :
    (presheaf F n).obj U = obj F n U := sorry

/-- The morphism of sectionwise symmetric-power presheaves induced by a morphism of module
sheaves. -/
@[stacks 01CG "map on sectionwise symmetric powers on a ringed space"]
noncomputable abbrev presheafMap {X : RingedSpace.{u}} {F G : X.Modules}
    (f : F ⟶ G) (n : ℕ) : presheaf F n ⟶ presheaf G n :=
  SheafOfModules.RingedSite.SymmetricPower.presheafMap X.sheaf f n

/-- The degree-`n` symmetric-power functor on module sheaves over a ringed space. -/
@[stacks 01CG "symmetric-power functor on a ringed space"]
noncomputable def functor (X : RingedSpace.{u}) (n : ℕ) :
    CategoryTheory.Functor X.Modules X.Modules :=
  SheafOfModules.RingedSite.SymmetricPower.functor X.sheaf n

/-- The degree-`n` symmetric-power sheaf of `F`. -/
@[stacks 01CG "symmetric power of a module sheaf"]
noncomputable abbrev sheaf {X : RingedSpace.{u}} (F : X.Modules) (n : ℕ) : X.Modules :=
  SheafOfModules.RingedSite.SymmetricPower.sheaf X.sheaf F n

/-- The symmetric-power sheaf is the sheafification of the sectionwise degree-`n`
symmetric-power presheaf. -/
@[stacks 01CG "symmetric power as a sheafification"]
theorem sheaf_eq_sheafification {X : RingedSpace.{u}}
    (F : X.Modules) (n : ℕ) :
    sheaf F n = (moduleSheafification X).obj (presheaf F n) := sorry

/-- The canonical isomorphism from the sheafification model to the symmetric-power sheaf. -/
@[stacks 01CG "canonical ringed-space symmetric-power sheafification isomorphism"]
noncomputable abbrev sheafificationIso {X : RingedSpace.{u}}
    (F : X.Modules) (n : ℕ) :
    (moduleSheafification X).obj (presheaf F n) ≅ sheaf F n :=
  SheafOfModules.RingedSite.SymmetricPower.sheafificationIso (𝒪 := X.sheaf) F n

/-- The morphism on degree-`n` symmetric-power sheaves induced by a morphism of module sheaves. -/
@[stacks 01CG "map on symmetric powers on a ringed space"]
noncomputable abbrev map {X : RingedSpace.{u}} {F G : X.Modules}
    (f : F ⟶ G) (n : ℕ) : sheaf F n ⟶ sheaf G n :=
  SheafOfModules.RingedSite.SymmetricPower.map X.sheaf f n

/-- The isomorphism on symmetric-power sheaves induced by a module-sheaf isomorphism. -/
@[stacks 01CG "ringed-space symmetric power of a module-sheaf isomorphism"]
noncomputable abbrev mapIso {X : RingedSpace.{u}} {F G : X.Modules}
    (e : F ≅ G) (n : ℕ) : sheaf F n ≅ sheaf G n :=
  SheafOfModules.RingedSite.SymmetricPower.mapIso (𝒪 := X.sheaf) e n

/-- On underlying presheaves, the symmetric-power sheaf map is the sheafification of the
sectionwise symmetric-power map. -/
@[stacks 01CG "symmetric-power map as a sheafification on a ringed space"]
theorem map_eq_sheafification {X : RingedSpace.{u}} {F G : X.Modules}
    (f : F ⟶ G) (n : ℕ) :
    map f n = (moduleSheafification X).map (presheafMap f n) := sorry

end AlgebraicGeometry.RingedSpace.SymmetricPower

scoped[AlgebraicGeometry] notation3:max "Sym[" n "] " F =>
  AlgebraicGeometry.RingedSpace.SymmetricPower.sheaf F n
