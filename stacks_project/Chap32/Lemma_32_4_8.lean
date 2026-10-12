/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.ClosedSubsets
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
variable [∀ i, CompactSpace (D.obj i)]
variable [∀ i, QuasiSeparatedSpace (D.obj i)]
variable [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))]

/- Lemma 32.4.8: in Situation `32.4.5`, if each stage `S_i = D.obj i` is equipped with a
nonempty closed subset `Z_i` compatible with the transition morphisms
`f_{i',i} = D.map (homOfLE hii')`, then there exists a point of the limit scheme `S = c.pt`
whose image in every stage lies in `Z_i`. -/
@[stacks 01Z3] #check
  (AlgebraicGeometry.Scheme.Limit.exists_point_mem_closed_of_compatible D c hc :
    ∀ (Z : ∀ i : I, Set (D.obj i))
      (hZ_closed : ∀ i, IsClosed (Z i))
      (hZ_nonempty : ∀ i, (Z i).Nonempty)
      (hZ_compat : ∀ {i i' : I} (hii' : i ≤ i'),
        Set.MapsTo (D.map (homOfLE hii')) (Z i') (Z i)),
      ∃ s : c.pt, ∀ i, (c.π.app i) s ∈ Z i)

end

end AlgebraicGeometry
