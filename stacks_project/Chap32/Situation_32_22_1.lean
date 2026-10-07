module

import StacksCheckRecall
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Noetherian

open CategoryTheory Limits AlgebraicGeometry

universe u

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
variable (i i' : I) (hii' : i ≤ i')
variable [∀ j, IsNoetherian (D.obj j)]
variable [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]

/- Situation 32.22.1: let `S = lim_i S_i` be the limit of a directed system of Noetherian
schemes with affine transition morphisms `S_{i'} ⟶ S_i` for `i ≤ i'`. In the canonical Lean
owner, this is a diagram `D : OrderDual I ⥤ Scheme`, a limit cone `c` with witness `hc`,
stagewise instances `IsNoetherian (D.obj i)`, and affine transition instances
`IsAffineHom (D.map (homOfLE hii'))`. -/
@[stacks 0CNM] #check (CategoryTheory.Limits.IsLimit c : Type (u + 1))

#check (hc : CategoryTheory.Limits.IsLimit c)
#check (c.pt : Scheme.{u})
#check (c.π.app i : c.pt ⟶ D.obj i)
#check (inferInstance : IsNoetherian (D.obj i))
#check (D.map (homOfLE hii') : D.obj i' ⟶ D.obj i)
#check (inferInstance : IsAffineHom (D.map (homOfLE hii')))

end
