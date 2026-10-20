module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.OpenImmersion

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The quasi-coherent subobjects of a scheme module that are of finite type. -/
def finiteTypeQuasiCoherentSubobjects (F : X.Modules) : Set (Subobject F) :=
  { G | ((G : X.Modules)).IsQuasicoherent ∧ ((G : X.Modules)).IsFiniteType }

/-- A subobject belongs to `finiteTypeQuasiCoherentSubobjects F` exactly when its underlying
module is quasi-coherent and of finite type. -/
@[simp] theorem mem_finiteTypeQuasiCoherentSubobjects
    (F : X.Modules) (G : Subobject F) :
    G ∈ finiteTypeQuasiCoherentSubobjects F ↔
      ((G : X.Modules)).IsQuasicoherent ∧ ((G : X.Modules)).IsFiniteType :=
  Iff.rfl

/-- On a quasi-compact quasi-separated scheme, the finite-type quasi-coherent subobjects of a
quasi-coherent module are directed by inclusion and have supremum the whole module. -/
theorem finiteTypeQuasiCoherentSubobjects_isDirectedColimit
    [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent] :
    DirectedOn (· ≤ ·) (finiteTypeQuasiCoherentSubobjects F) ∧
      IsLUB (finiteTypeQuasiCoherentSubobjects F) (⊤ : Subobject F) := sorry

end AlgebraicGeometry.Scheme.Modules

end
