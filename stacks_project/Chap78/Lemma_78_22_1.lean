module

public import stacks_project.Chap78.Lemma_78_22_1_Isom

/-!
# Isom sheaves of a quotient stack

This file records the identification of `Isom(π(x'), π(y'))` on `[U/R]` with the sheaf of
points of `S' ×_{(y', x'), U ×_S U} R` over `S'`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace GroupoidAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Lemma 78.22.1. Assume `B → S`, `(U, R, s, t, c)` and `π : 𝒮_U ⟶ [U/R]` are as in
Lemma 78.20.2. Let `S'` be a scheme over `S`. If `x = π(x')` and `y = π(y')` for morphisms
`x', y' : S' ⟶ U`, then `Isom(x, y)` equals `S' ×_{(y', x'), U ×_S U} R` as sheaves over
`S'`. Since `[U/R]` is a stack in groupoids, `Isom(x, y)` is the Hom sheaf of the quotient
stack, and the right-hand side is the sheaf of `S'`-points of `isomPullback G x' y'`. -/
@[stacks 044V]
theorem sheafHom_atlas_isIsomorphic_isomPullback
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left) :
    IsIsomorphic
      ((Functor.fiberPseudofunctor (quotientStack G).p).sheafHom
        (Scheme.fppfTopology.over S)
        (((atlas G).fiberFunctor S').obj (objOfHom x'))
        (((atlas G).fiberFunctor S').obj (objOfHom y')))
      (isomPullbackSheaf G x' y') :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
