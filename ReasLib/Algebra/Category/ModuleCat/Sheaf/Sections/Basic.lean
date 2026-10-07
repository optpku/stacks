module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Sections of sheaves of modules

This file provides the coefficient-generic evaluation surface for module sheaves over a sheaf of
rings on a topological space.
-/

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace

universe u

namespace SheafOfModules

variable {X : TopCat.{u}} {𝒪 : X.Sheaf RingCat.{u}}

/-- The additive group of sections of a module sheaf on an open subset. -/
abbrev sectionsOnOpen (F : SheafOfModules 𝒪) (U : Opens X) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (F.val.obj (op U))

namespace Hom

/-- A morphism of module sheaves evaluated on sections over an open subset. -/
abbrev app {F G : SheafOfModules 𝒪} (f : F ⟶ G) (U : Opens X) :
    sectionsOnOpen F U ⟶ sectionsOnOpen G U :=
  AddCommGrpCat.ofHom ((f.val.app (op U)).hom)

end Hom

end SheafOfModules
