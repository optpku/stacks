module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.Separated
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 70.5.9: in Situation `70.5.5`, if the limit algebraic space `X` is
absolutely separated (Stacks "separated"), then some stage `X_i` is absolutely
separated. -/
@[stacks 084T] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.exists_isSeparated_of_isLimit :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
      (c : Cone D) (hc : IsLimit c)
      [∀ j, IsQuasiCompact (D.obj j)]
      [∀ j, IsAbsolutelyQuasiSeparated (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
      [IsAbsolutelySeparated c.pt],
      ∃ i : I, IsAbsolutelySeparated (D.obj i))
