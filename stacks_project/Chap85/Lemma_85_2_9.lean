module

public import stacks_project.Chap85.Lemma_85_2_9_Zariski

/-!
# Lemma 85.2.9
-/

@[expose] public section

open CategoryTheory AlgebraicTopology HomologicalComplex
open AlgebraicTopology.SimplicialSpace

universe u

namespace AlgebraicTopology.SimplicialSpace.Zariski

/-- Lemma 85.2.9: let `X` be a simplicial topological space. The complex of abelian
presheaves on `Zariski X` with terms `Z_{X_n} = FreeAbelianYoneda.obj (Zariski.top X ⦋n⦌)`
and boundary maps the alternating face sums is a resolution of the constant presheaf `ℤ`. -/
@[stacks 09W5]
instance augmentation_quasiIso (X : SimplicialObject TopCat.{u}) :
    QuasiIso (augmentation X) := sorry

end AlgebraicTopology.SimplicialSpace.Zariski
