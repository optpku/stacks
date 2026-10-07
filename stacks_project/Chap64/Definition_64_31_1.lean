module

public import ReasLib.NumberTheory.FunctionField.Adele
public import ReasLib.NumberTheory.Automorphic.CuspForm
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry

/- Definition 64.31.1. Let `k` be a finite field of characteristic `p` and let
`X` be a geometrically irreducible smooth projective curve over `k`, with
function field `K = k(X)`. Write `A` for the restricted product of the
completions `K_v` at closed points and `O` for the product of the integer
rings `O_v`. For a coefficient ring `Λ` in which `p` is invertible, an
unramified cusp form on `GL (Fin 2) A` with values in `Λ` is a function
`f : GL (Fin 2) A → Λ` which is right `GL (Fin 2) K`-invariant, left
`GL (Fin 2) O`-invariant, and whose unipotent integrals over `A / K` vanish.
This is `UnramifiedCuspForm`. -/
@[stacks 03VS] #check
  (AlgebraicGeometry.SchemeOverField.UnramifiedCuspForm :
    ∀ {k : Type*} [Field k] (X : SchemeOverField k)
      [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
      (Λ : Type _) [Ring Λ] [Fintype k] [Invertible (ringChar k : Λ)], Type _)
