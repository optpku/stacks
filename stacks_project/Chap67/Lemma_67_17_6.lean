module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.SchemeTheoreticDensity.Intersection
import StacksCheckRecall

/-!
# Intersection of scheme-theoretically dense open subspaces

The intersection of two scheme-theoretically dense open immersions of
algebraic spaces remains scheme-theoretically dense.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.17.6: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
If `ιU` and `ιV` are scheme-theoretically dense open immersions into `X`, then
so is the inclusion `openInverseImageι ιU ιV ≫ ιU` of the open subspace
`U ∩ V` into `X`. -/
@[stacks 0837] #check (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticallyDense.inf :
  ∀ {S : Scheme.{u}} {X U V : AlgebraicSpace S}
    (ιU : U ⟶ X) (ιV : V ⟶ X) [IsOpenImmersion ιU] [IsOpenImmersion ιV]
    [IsSchemeTheoreticallyDense ιU] [IsSchemeTheoreticallyDense ιV],
    IsSchemeTheoreticallyDense (openInverseImageι ιU ιV ≫ ιU))

#check (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticallyDense.of_inf :
  ∀ {S : Scheme.{u}} {X U V : AlgebraicSpace S}
    {ιU : U ⟶ X} {ιV : V ⟶ X} [IsOpenImmersion ιU] [IsOpenImmersion ιV]
    (hU : IsSchemeTheoreticallyDense ιU)
    (hV : IsSchemeTheoreticallyDense ιV),
    IsSchemeTheoreticallyDense (openInverseImageι ιU ιV ≫ ιU))
