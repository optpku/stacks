/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.DirectedLimit
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.FundamentalGroup
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.FundamentalGroupLimit

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

/- Lemma 58.14.1 (1): for a directed inverse system of quasi-compact and quasi-separated
schemes with affine transitions and limit cone `c`, the canonical finite étale comparison
from the categorical colimit of the stage categories to the category of the limit
is an equivalence. -/
@[stacks 0BTV] #check (AlgebraicGeometry.Scheme.finiteEtale_colimit_equivalence :
  ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j).carrier]
    [∀ j, QuasiSeparatedSpace (D.obj j).carrier]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))],
    (Scheme.finiteEtaleColimitComparison D c).IsEquivalence)

/- Lemma 58.14.1 (2): for eventually connected stages and a geometric point of the
limit, the canonical comparison from its étale fundamental group to the
inverse limit of the connected-tail stage groups is an isomorphism. -/
@[stacks 0BTV] #check (AlgebraicGeometry.Scheme.fundamentalGroup_limitIso :
  ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j).carrier]
    [∀ j, QuasiSeparatedSpace (D.obj j).carrier]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (xbar : Scheme.GeometricPoint c.pt) (i₀ : I)
    (hconn : ∀ i : I, i₀ ≤ i → ConnectedSpace (D.obj i).carrier),
    IsIso (Scheme.fundamentalGroupLimitComparison D c hc xbar i₀ hconn))
