module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Finite-type quasi-coherent subobjects

On a quasi-compact quasi-separated algebraic space, every quasi-coherent module is the
directed colimit of its finite-type quasi-coherent submodules.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The finite-type quasi-coherent subobjects of a module on an algebraic space. -/
def finiteTypeQuasiCoherentSubobjects (F : X.Modules) : Set (Subobject F) :=
  {G | ((G : X.Modules)).IsQuasicoherent ∧ ((G : X.Modules)).IsFiniteType}

/-- A subobject belongs to `finiteTypeQuasiCoherentSubobjects F` exactly when its underlying
module is quasi-coherent and of finite type. -/
@[simp] theorem mem_finiteTypeQuasiCoherentSubobjects (F : X.Modules) (G : Subobject F) :
    G ∈ finiteTypeQuasiCoherentSubobjects F ↔
      ((G : X.Modules)).IsQuasicoherent ∧ ((G : X.Modules)).IsFiniteType :=
  Iff.rfl

/-- On a quasi-compact quasi-separated algebraic space, the finite-type quasi-coherent subobjects
of a quasi-coherent module are directed by inclusion and have supremum the whole module. -/
theorem finiteTypeQuasiCoherentSubobjects_isDirectedColimit [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X] (F : X.Modules) [F.IsQuasicoherent] :
    DirectedOn (· ≤ ·) (finiteTypeQuasiCoherentSubobjects F) ∧
      IsLUB (finiteTypeQuasiCoherentSubobjects F) (⊤ : Subobject F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
