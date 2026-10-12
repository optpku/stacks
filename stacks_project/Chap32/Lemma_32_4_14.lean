/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Separated
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

/- Lemma 32.4.14: in Situation `32.4.5`, if the limit scheme is separated, then after
passing to some stage `i₀`, every later stage is separated. -/
@[stacks 086Q] #check
  (AlgebraicGeometry.Scheme.Limit.exists_eventually_isSeparated_of_isLimit :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ j, CompactSpace (D.obj j)]
      [∀ j, QuasiSeparatedSpace (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
      [c.pt.IsSeparated],
      ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → (D.obj i).IsSeparated)
