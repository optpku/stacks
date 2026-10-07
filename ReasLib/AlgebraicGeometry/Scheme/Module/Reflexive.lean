module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Reflexive module sheaves

This file defines the dual and reflexive hull of a module sheaf using the internal Hom into the
monoidal unit. It also provides the canonical map from a module sheaf to its double dual and the
predicate that this map is an isomorphism.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

section

variable {X : Scheme.{u}}

/-- The dual of a module sheaf is its internal Hom into the monoidal unit. -/
abbrev dual (ℱ : X.Modules) : X.Modules :=
  (ihom ℱ).obj (𝟙_ X.Modules)

/-- The reflexive hull of a module sheaf is its double dual. -/
@[stacks 0AVU "reflexive hull"]
abbrev reflexiveHull (ℱ : X.Modules) : X.Modules :=
  dual (dual ℱ)

/-- The dual reverses morphisms of module sheaves. -/
noncomputable abbrev dualMap {ℱ 𝒢 : X.Modules} (f : ℱ ⟶ 𝒢) :
    dual 𝒢 ⟶ dual ℱ :=
  (MonoidalClosed.pre f).app (𝟙_ X.Modules)

/-- The reflexive-hull construction maps morphisms by dualizing twice. -/
noncomputable abbrev reflexiveHullMap {ℱ 𝒢 : X.Modules} (f : ℱ ⟶ 𝒢) :
    reflexiveHull ℱ ⟶ reflexiveHull 𝒢 :=
  dualMap (dualMap f)

/-- The canonical morphism from a module sheaf to its reflexive hull is induced by evaluation. -/
@[stacks 0AVU "canonical map"]
noncomputable def toReflexiveHull (ℱ : X.Modules) :
    ℱ ⟶ reflexiveHull ℱ :=
  MonoidalClosed.curry
    ((β_ (dual ℱ) ℱ).hom ≫ (ihom.ev ℱ).app (𝟙_ X.Modules))

/-- A module sheaf is reflexive when its canonical morphism to the double dual is an isomorphism. -/
@[stacks 0AVU "reflexive predicate"]
abbrev IsReflexive (ℱ : X.Modules) : Prop :=
  IsIso (toReflexiveHull ℱ)

/-- Double dualization preserves identity morphisms. -/
theorem reflexiveHullMap_id (ℱ : X.Modules) :
    reflexiveHullMap (𝟙 ℱ) = 𝟙 (reflexiveHull ℱ) := sorry

/-- Double dualization preserves composition of morphisms. -/
theorem reflexiveHullMap_comp {ℱ 𝒢 ℋ : X.Modules} (f : ℱ ⟶ 𝒢) (g : 𝒢 ⟶ ℋ) :
    reflexiveHullMap (f ≫ g) = reflexiveHullMap f ≫ reflexiveHullMap g := sorry

/-- Double dualization, regarded as an endofunctor on module sheaves. -/
noncomputable def reflexiveHullFunctor (X : Scheme.{u}) : X.Modules ⥤ X.Modules where
  obj := reflexiveHull
  map := reflexiveHullMap
  map_id := reflexiveHullMap_id
  map_comp := reflexiveHullMap_comp

/-- The canonical maps to double duals form a natural transformation. -/
noncomputable def toReflexiveHullNatTrans (X : Scheme.{u}) :
    𝟭 X.Modules ⟶ reflexiveHullFunctor X where
  app := toReflexiveHull
  naturality := sorry

/-- The tensor unit of scheme modules is reflexive. -/
instance instIsReflexiveTensorUnit (X : Scheme.{u}) :
    IsReflexive (𝟙_ X.Modules) := sorry

end

end AlgebraicGeometry.Scheme.Modules
