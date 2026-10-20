module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.Affine
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 70.5.10: in Situation `70.5.5`, if the limit algebraic space `X` is
affine, then some stage `X_i` is affine; in fact, after passing to a sufficiently
late stage `i₀`, every later stage is affine. -/
@[stacks 07SQ] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.exists_isAffine_of_isLimit :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
      (c : Cone D) (hc : IsLimit c)
      [∀ j, IsQuasiCompact (D.obj j)]
      [∀ j, IsAbsolutelyQuasiSeparated (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
      [AlgebraicSpace.IsAffine c.pt],
      ∃ i : I, AlgebraicSpace.IsAffine (D.obj i))
