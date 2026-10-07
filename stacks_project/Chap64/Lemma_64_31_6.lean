module

public import ReasLib.NumberTheory.Automorphic.CuspForms.Algebraicity
import StacksCheckRecall

universe u v

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.SchemeOverField.CuspForms
open TopologicalSpace

/- Lemma 64.31.6. Algebraicity of eigenvalues. If `Λ` is a field, the eigenvalues `t_v` for
`f ∈ C(Λ)` are algebraic over the prime subfield `⊥ ⊂ Λ`; the character is
prime-subfield-valued and extended to `Λ`. -/
@[stacks 03VX] #check
  (AlgebraicGeometry.SchemeOverField.CuspForms.heckeT_eigenvalue_isAlgebraic :
    ∀ {k : Type u} [Field k] [Fintype k]
      (X : SchemeOverField k)
      [Curve X] [Smooth X.hom] [Projective X.hom]
      [GeometricallyIrreducible X.hom]
      {Λ : Type v} [Field Λ] [Invertible (ringChar k : Λ)]
      (character : closedPoints X.left → (⊥ : Subfield Λ)ˣ)
      (v : closedPoints X.left) {t : Λ},
      Module.End.HasEigenvalue
        (heckeT
          (Units.map (algebraMap (⊥ : Subfield Λ) Λ).toMonoidHom ∘ character) v) t →
        IsAlgebraic (⊥ : Subfield Λ) t)
