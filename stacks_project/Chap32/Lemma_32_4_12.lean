/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.QuasiAffine
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

/- Lemma 32.4.12: In Situation 32.4.5 if `S` is quasi-affine, then for some `i₀ : I`
the schemes `Sᵢ` for `i₀ ≤ i` are quasi-affine. -/
@[stacks 01Z5] #check
  (AlgebraicGeometry.Scheme.Limit.exists_eventually_isQuasiAffine_of_isLimit :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ j, CompactSpace (D.obj j)]
      [∀ j, QuasiSeparatedSpace (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
      (hS : c.pt.IsQuasiAffine),
      ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → (D.obj i).IsQuasiAffine)
