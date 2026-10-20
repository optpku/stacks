module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.CategoryTheory.Subobject.Basic
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.FiniteTypeGeneration

/-!
# Finite-type quasi-coherent subobjects

On a quasi-compact quasi-separated algebraic space, every quasi-coherent module is the
directed colimit of its finite-type quasi-coherent submodules.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.finiteTypeQuasiCoherentSubobjects :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules), Set (Subobject F))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mem_finiteTypeQuasiCoherentSubobjects :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) (G : Subobject F),
    G ∈ AlgebraicGeometry.AlgebraicSpace.Modules.finiteTypeQuasiCoherentSubobjects F ↔
      ((G : X.Modules)).IsQuasicoherent ∧ ((G : X.Modules)).IsFiniteType)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.finiteTypeQuasiCoherentSubobjects_isDirectedColimit :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X] (F : X.Modules) [F.IsQuasicoherent],
    DirectedOn (· ≤ ·)
        (AlgebraicGeometry.AlgebraicSpace.Modules.finiteTypeQuasiCoherentSubobjects F) ∧
      IsLUB (AlgebraicGeometry.AlgebraicSpace.Modules.finiteTypeQuasiCoherentSubobjects F)
        (⊤ : Subobject F))
