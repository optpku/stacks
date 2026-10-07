module

public import Mathlib.LinearAlgebra.Projectivization.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.VectorSpace
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.Basic

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.VectorSpace.ProjectiveEndomorphism

variable {k : Type u} [Field k]
variable {V : Type u} [AddCommGroup V] [Module k V]

/-- Projective classes of nonzero endomorphisms of `V`. -/
abbrev Space (k : Type u) [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] :=
  Projectivization k (Module.End k V)

/-- The symmetric-algebra map induced by an endomorphism preserves the grading by powers of
degree-one elements. -/
theorem gradedMap_mem (g : Module.End k V) {d : ℕ}
    {x : SymmetricAlgebra k V} (hx : x ∈ grading k V d) :
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι k V).comp g) x ∈ grading k V d := sorry

/-- The graded symmetric-algebra map induced by an endomorphism. -/
def gradedMap (g : Module.End k V) : grading k V →+*ᵍ grading k V where
  toRingHom := SymmetricAlgebra.lift ((SymmetricAlgebra.ι k V).comp g)
  map_mem := gradedMap_mem g

/-- The chosen nonzero representative of a projective endomorphism class. -/
abbrev representative (g : Space k V) : Module.End k V :=
  g.rep

/-- The natural domain `U_g` of the rational projective map induced by `[g]`. -/
abbrev domain (g : Space k V) : (scheme k V).Opens :=
  projMapDomain (gradedMap (representative g))

/-- The rational projective map `r_g : U_g ⟶ ℙ(V)` induced by `[g]`. -/
def hom (g : Space k V) : (domain g).toScheme ⟶ scheme k V :=
  projMapMap (gradedMap (representative g))

/-- The closed image of a subset of `ℙ(V)` under the rational projective map induced by `[g]`. -/
def image (g : Space k V) (X : Set (scheme k V)) :
    TopologicalSpace.Closeds (scheme k V) :=
  TopologicalSpace.Closeds.closure
    ((hom g).base '' ((domain g).ι.base ⁻¹' X))

/-- The projective class `[id_V]`. -/
def identity [Nontrivial V] : Space k V :=
  Projectivization.mk k (1 : Module.End k V) one_ne_zero

end AlgebraicGeometry.ProjectiveSpace.VectorSpace.ProjectiveEndomorphism
