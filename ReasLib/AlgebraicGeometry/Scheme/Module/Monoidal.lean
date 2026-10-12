/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Monoidal
public import ReasLib.Topology.Sheaves.Abelian.Sheafification

/-!
# Monoidal scheme-module support

The category `X.Modules` is definitionally the category of module sheaves over the underlying
ring sheaf of `X`.  This file specializes the canonical tensor product, symmetry, and local
internal Hom constructed for a commutative ringed site.  Thus scheme-level applications share
one data owner with generic ringed-site and ringed-space APIs.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open SheafOfModules.RingedSite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The canonical tensor product on scheme modules, specialized from the commutative-ringed-site
construction because typeclass search does not unfold `Scheme.Modules` automatically. -/
@[instance_reducible, instance, stacks 03L6 "canonical tensor product on scheme modules"]
noncomputable def instMonoidalCategory (X : Scheme.{u}) :
    MonoidalCategory X.Modules :=
  RingedSpace.modulesMonoidalCategory X.toRingedSpace

/-- The canonical tensor symmetry on scheme modules, specialized from the same ringed-site
owner. -/
@[instance_reducible, instance, stacks 03L6 "canonical symmetry on scheme modules"]
noncomputable def instSymmetricCategory (X : Scheme.{u}) :
    SymmetricCategory X.Modules :=
  RingedSpace.modulesSymmetricCategory X.toRingedSpace

/-- The tensor product of scheme modules is additive in both variables. -/
@[instance, stacks 03EP "additive tensor product on scheme modules"]
theorem instMonoidalPreadditive (X : Scheme.{u}) :
    MonoidalPreadditive X.Modules :=
  SheafOfModules.RingedSite.monoidalPreadditive
    (J := Opens.grothendieckTopology X.toTopCat) (O := X.𝒪)

/-- The canonical closed structure on scheme modules.  Its right adjoints are the explicit local
internal-Hom functors constructed for the underlying commutative ringed site. -/
@[instance_reducible, instance, stacks 03EM "canonical internal Hom on scheme modules"]
noncomputable def instMonoidalClosed (X : Scheme.{u}) :
    MonoidalClosed X.Modules :=
  SheafOfModules.RingedSite.InternalHom.monoidalClosed
    (J := Opens.grothendieckTopology X.toTopCat) X.𝒪

/-- The internal Hom of two scheme modules, specialized from the canonical closed structure. -/
noncomputable abbrev internalHom (ℱ 𝒢 : X.Modules) : X.Modules :=
  (ihom ℱ).obj 𝒢

/- This spelling remains temporarily for source files that have not yet dropped their redundant
per-object parameter.  It is transparent and owns no data; new APIs should rely on the canonical
`instMonoidalClosed` above. -/
/-- Compatibility spelling for the canonical closed structure in the underlying ringed-space
presentation of a scheme module. -/
@[deprecated "Use `Closed F` with the canonical scheme-module monoidal structure." (since := "2026-08-06")]
abbrev RingedSpaceClosed (F : X.Modules) :=
  @Closed (RingedSpace.Modules X.toRingedSpace)
    SheafOfModules.instCategory
    (SheafOfModules.RingedSite.moduleMonoidalCategory
      (J := Opens.grothendieckTopology X.toRingedSpace) X.toRingedSpace.sheaf) F

end AlgebraicGeometry.Scheme.Modules
