module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.LinearProjection

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.VectorSpace

variable {k : Type u} [Field k]
variable {V : Type u} [AddCommGroup V] [Module k V]

/- The compatibility import exposes the complete restricted linear-projection operation. -/
#check (AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearProjection.restrict :
  {p : scheme k V} → (r : LinearProjection k V p) →
    {X : Scheme.{u}} → (i : X ⟶ scheme k V) →
      (hi : Set.range i.base ⊆ Set.range r.domain.ι) → X ⟶ r.target)

end AlgebraicGeometry.ProjectiveSpace.VectorSpace
