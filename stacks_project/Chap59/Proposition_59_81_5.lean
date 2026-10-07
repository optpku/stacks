module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.AbsolutelyIntegrallyClosed
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Proposition 59.81.5: if `R` is absolutely integrally closed and `M` is a finite
abelian group, then étale cohomology `H^i(Spec R, underline M)` vanishes for all
`i > 0`, where `underline M` is the constant étale sheaf associated to `M`. -/
@[stacks 0GY7] #check
  (AlgebraicGeometry.Scheme.etaleCohomology_constant_isZero_of_isAbsolutelyIntegrallyClosed :
    ∀ {R M : Type u} [CommRing R] [IsAbsolutelyIntegrallyClosed R]
      [AddCommGroup M] [Finite M]
      [HasSheafify (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u})]
      {i : ℕ} (hi : 0 < i),
    IsZero
      ((Sheaf.functorH (Spec (.of R)).smallEtaleTopology i).obj
        ((constantSheaf (Spec (.of R)).smallEtaleTopology AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} M)))))
