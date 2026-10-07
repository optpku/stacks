module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DirectedAffine.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Descent
import StacksCheckRecall

/-!
# The comparison `U/R ⟶ lim X_i` of fppf sheaves
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

/- 70.4.1.1: The natural comparison from the quotient of the limiting atlas by its
limiting kernel-pair relation to the inverse limit is an isomorphism of fppf sheaves. -/
@[stacks 07SG] #check
  (AlgebraicGeometry.AlgebraicSpace.DirectedAffine.quotientToSheafLimit_isIso :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S) (i0 : I)
      (P : Presentation (D.obj (OrderDual.toDual i0)))
      [h_affine : ∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))],
      IsIso (AlgebraicGeometry.AlgebraicSpace.DirectedAffine.quotientToSheafLimit D i0 P))

#check (AlgebraicGeometry.Scheme.PreRelation.isIso_quotientSheafToCoequalizer :
  ∀ {S : Scheme.{u}} {U : Over S} (J : GrothendieckTopology (Over S))
    [J.Subcanonical] (P : Scheme.PreRelation U),
    IsIso (Scheme.PreRelation.quotientSheafToCoequalizer J P))
