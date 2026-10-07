module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.Colimit
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 87.9.9: for a scheme `S` and a weakly admissible topological ring
`A` over `S`, the formal spectrum of `A` is the affine formal algebraic space
`spf A structureHom`, the colimit of `Spec(A ⧸ I)` over weak ideals of definition
of `A`, formed in `Sheaf (Scheme.fppfTopology.over S) (Type u)`. -/
@[stacks 0AIF] #check (AlgebraicGeometry.AffineFormalAlgebraicSpace.spf :
  ∀ (A : Type u) [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyAdmissibleRing A] {S : Scheme.{u}},
    (Spec (.of A) ⟶ S) → ∀ [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)],
    Sheaf (Scheme.fppfTopology.over S) (Type u))
