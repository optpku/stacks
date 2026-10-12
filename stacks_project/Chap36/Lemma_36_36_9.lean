/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ResolutionProperty.Limit
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Limit

/- Lemma 36.36.9: a directed inverse limit of quasi-compact, quasi-separated schemes with
affine transition morphisms has the resolution property if and only if some stage does. -/
@[stacks 0F8B] #check (AlgebraicGeometry.Scheme.Limit.hasResolutionProperty_iff_exists_stage :
  ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))],
      HasResolutionProperty c.pt ↔ ∃ i : I, HasResolutionProperty (D.obj i))

end AlgebraicGeometry.Scheme.Limit
