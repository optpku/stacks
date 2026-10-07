module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.NoetherNormalization

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.18.2: let `f : X ⟶ S` be a finite type morphism of affine schemes, let `s : S`, and
assume the fiber `X_s` has topological Krull dimension `d`. Then `f` factors through the relative
affine `d`-space over `S`, and the induced morphism from the fiber of `X` over `s` to the fiber of
`𝔸(Fin d; S) ↘ S` over `s` is finite. -/
@[stacks 0CBI] #check
  (AlgebraicGeometry.Scheme.Hom.exists_affineSpace_factorization_finite_on_fiber :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine X] [IsAffine S] [Scheme.Hom.FiniteType f]
      (s : S) (d : ℕ) (hfdim : topologicalKrullDim (f.fiber s) = d),
      ∃ π : X ⟶ AffineSpace (ULift.{u} (Fin d)) S,
        ∃ hπ : π ≫ (AffineSpace (ULift.{u} (Fin d)) S ↘ S) = f,
          IsFinite
            ((eqToHom
                (congrArg (fun φ ↦ Scheme.Hom.fiber φ s) hπ.symm)) ≫
              Scheme.Hom.compFiberToBaseFiber π
                (AffineSpace (ULift.{u} (Fin d)) S ↘ S) s))
