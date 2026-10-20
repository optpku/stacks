/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Hom
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The Glued-Module Functor

This leaf packages the module of compatible local sections as a functor from
principal-open module gluing data to modules over the base ring.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace LocalizedModule.Away.Gluing

variable {R : Type u} [CommRing R]
variable {ι : Type w}
variable {f : ι → R}

/-- The map induced by the identity gluing morphism is the identity morphism
of the corresponding bundled glued module. -/
@[stacks 00EK "principal-open glued-module functor identity"]
theorem gluedModuleFunctor_map_id (X : Gluing f) :
    ModuleCat.ofHom ((𝟙 X : X ⟶ X).gluedMap) =
      𝟙 (ModuleCat.of R X.gluedModule) := sorry

/-- The map induced by a composite gluing morphism is the composite of the
corresponding bundled glued-module maps. -/
@[stacks 00EK "principal-open glued-module functor composition"]
theorem gluedModuleFunctor_map_comp {X Y Z : Gluing f}
    (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    ModuleCat.ofHom ((φ ≫ ψ).gluedMap) =
      ModuleCat.ofHom φ.gluedMap ≫ ModuleCat.ofHom ψ.gluedMap := sorry

/-- Tag `00EK`: the functor sending principal-open module gluing data to its
module of compatible local sections. -/
@[stacks 00EK "principal-open glued-module functor"]
noncomputable def gluedModuleFunctor :
    Gluing f ⥤ ModuleCat.{max u v w} R where
  obj X := ModuleCat.of R X.gluedModule
  map φ := ModuleCat.ofHom φ.gluedMap
  map_id := gluedModuleFunctor_map_id
  map_comp := gluedModuleFunctor_map_comp

end LocalizedModule.Away.Gluing
