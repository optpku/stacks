module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.DirectedAffine
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
variable [∀ {i j : OrderDual I} (f : i ⟶ j), IsAffineHom (D.map f)]
variable [∀ i : OrderDual I, Nonempty (D.obj i)]
variable [∀ i : OrderDual I, CompactSpace (D.obj i)]

/- Lemma 32.4.3: if `S = lim_i S_i` is the limit of a directed inverse system of schemes with
affine transition morphisms and every `S_i` is nonempty and quasi-compact, then `S` is
nonempty. -/
@[stacks 01Z2] #check
  (AlgebraicGeometry.Scheme.Limit.DirectedAffine.nonempty_of_isLimit D c hc :
    Nonempty c.pt)

end

end AlgebraicGeometry
