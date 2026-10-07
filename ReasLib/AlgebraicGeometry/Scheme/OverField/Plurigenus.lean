module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorPower
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- The `n`th plurigenus of a smooth scheme `X` over a field of relative dimension `d` is the
dimension of global sections of the `n`th tensor power of `Λ[d] Ω[X.hom.toShHom]`. -/
noncomputable def plurigenus {k : Type u} [Field k] (X : SchemeOverField k) (d n : ℕ)
    [SmoothOfRelativeDimension d X.hom] : ℕ :=
  Scheme.Hom.cohomologyFinrank X.hom
    (RingedSpace.TensorPower.sheaf (Λ[d] Ω[X.hom.toShHom]) n) 0

/-- `plurigenus X d n` is the degree-zero cohomology finrank of the `n`th tensor power of
`Λ[d] Ω[X.hom.toShHom]`. -/
theorem plurigenus_def {k : Type u} [Field k] (X : SchemeOverField k) (d n : ℕ)
    [SmoothOfRelativeDimension d X.hom] :
    plurigenus X d n =
      Scheme.Hom.cohomologyFinrank X.hom
        (RingedSpace.TensorPower.sheaf (Λ[d] Ω[X.hom.toShHom]) n) 0 := sorry

/-- The plurigenera of smooth proper varieties over a field are invariant under birational
equivalence over that field. -/
theorem plurigenus_eq_of_birational {k : Type u} [Field k] (d : ℕ)
    (X Y : SchemeOverField k) [Variety X] [Variety Y] [IsProper X.hom] [IsProper Y.hom]
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension d Y.hom]
    (h : Scheme.BirationalOver X.hom Y.hom) (n : ℕ) :
    plurigenus X d n = plurigenus Y d n := sorry

end AlgebraicGeometry.SchemeOverField
