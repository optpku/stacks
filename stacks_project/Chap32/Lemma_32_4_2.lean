module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.DirectedAffine
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
variable [∀ {i j : OrderDual I} (f : i ⟶ j), IsAffineHom (D.map f)]

/- Lemma 32.4.2: if `S = lim_i S_i` is the limit of a directed inverse system
of schemes with affine transition morphisms, then its underlying topological
space is the inverse limit of the underlying topological spaces of the stages. -/
@[stacks 0CUF]
#check
  (AlgebraicGeometry.isLimit_forgetToTop_mapCone_of_directedAffineTransition D c hc :
    IsLimit (Scheme.forgetToTop.mapCone c))
