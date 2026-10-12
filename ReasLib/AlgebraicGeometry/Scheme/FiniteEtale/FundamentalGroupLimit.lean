/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Conj
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.DirectedLimit
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.FundamentalGroup

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor
open AlgebraicGeometry
open scoped FintypeCatDiscrete

universe u

namespace AlgebraicGeometry.Scheme

/-- The upper tail of a preordered index set starting at a specified index. -/
abbrev connectedTail (I : Type u) [Preorder I] (i₀ : I) :=
  { i : I // i₀ ≤ i }

/-- The finite étale fiber functor pulled back along a leg of a scheme cone. -/
def finiteEtaleFiberViaCone {I : Type u} [Preorder I] {D : OrderDual I ⥤ Scheme.{u}}
    (c : Cone D) (xbar : GeometricPoint c.pt) (i : OrderDual I) :
    FiniteEtale (D.obj i) ⥤ FintypeCat.{u} :=
  finiteEtaleBaseChange (c.π.app i) ⋙ xbar.finiteFiber

/-- The scheme transition morphism induced by an arrow between indices in an upper tail. -/
def connectedTailSchemeHom {I : Type u} [Preorder I] (D : OrderDual I ⥤ Scheme.{u})
    {i₀ : I} {i j : OrderDual (connectedTail I i₀)} (arrow : i ⟶ j) :
    D.obj (OrderDual.toDual i.1) ⟶ D.obj (OrderDual.toDual j.1) :=
  D.map (homOfLE (leOfHom arrow))

/-- Cone-leg fiber functors are compatible with base change along a scheme transition. -/
def finiteEtaleFiberViaConeCompat {I : Type u} [Preorder I] {D : OrderDual I ⥤ Scheme.{u}}
    (c : Cone D) (xbar : GeometricPoint c.pt) {i₀ : I}
    {i j : OrderDual (connectedTail I i₀)} (arrow : i ⟶ j) :
    finiteEtaleBaseChange (connectedTailSchemeHom D arrow) ⋙
        finiteEtaleFiberViaCone c xbar (OrderDual.toDual i.1) ≅
      finiteEtaleFiberViaCone c xbar (OrderDual.toDual j.1) :=
  associator (finiteEtaleBaseChange (connectedTailSchemeHom D arrow))
      (finiteEtaleBaseChange (c.π.app (OrderDual.toDual i.1))) xbar.finiteFiber ≪≫
    isoWhiskerRight
      (MorphismProperty.Over.pullbackComp (c.π.app (OrderDual.toDual i.1))
        (connectedTailSchemeHom D arrow) (c.π.app (OrderDual.toDual j.1))
        (c.w (homOfLE (leOfHom arrow))).symm).symm
      xbar.finiteFiber

/-- The inverse system of profinite automorphism groups of cone-leg fiber functors on a
connected upper tail. -/
def etaleFundamentalGroupDiagram {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Scheme.{u}} (c : Cone D) (xbar : GeometricPoint c.pt) (i₀ : I)
    (hconn : ∀ i : I, i₀ ≤ i → ConnectedSpace (D.obj i).carrier) :
    OrderDual (connectedTail I i₀) ⥤ ProfiniteGrp where
  obj i := ProfiniteGrp.of (Aut (finiteEtaleFiberViaCone c xbar (OrderDual.toDual i.1)))
  map {i j} arrow :=
    ProfiniteGrp.ofHom
      ⟨(finiteEtaleFiberViaConeCompat c xbar arrow).conjAut.toMonoidHom.comp
        (((whiskeringLeft _ _ _).obj
          (finiteEtaleBaseChange (connectedTailSchemeHom D arrow))).mapAut
          (finiteEtaleFiberViaCone c xbar (OrderDual.toDual i.1))), sorry⟩
  map_id := sorry
  map_comp := sorry

/-- Each object of the connected-tail diagram is the automorphism group of the corresponding
cone-leg pullback of the finite étale fiber functor. -/
theorem etaleFundamentalGroupDiagram_obj {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Scheme.{u}} (c : Cone D) (xbar : GeometricPoint c.pt) (i₀ : I)
    (hconn : ∀ i : I, i₀ ≤ i → ConnectedSpace (D.obj i).carrier)
    (i : OrderDual (connectedTail I i₀)) :
    (etaleFundamentalGroupDiagram c xbar i₀ hconn).obj i =
      ProfiniteGrp.of (Aut (finiteEtaleFiberViaCone c xbar (OrderDual.toDual i.1))) :=
  rfl

/-- At a connected stage, the cone-leg automorphism group is isomorphic to the étale
fundamental group based at the image of the geometric point. -/
theorem etaleFundamentalGroupDiagram_obj_iso {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Scheme.{u}} (c : Cone D) (xbar : GeometricPoint c.pt) (i₀ : I)
    (hconn : ∀ i : I, i₀ ≤ i → ConnectedSpace (D.obj i).carrier)
    (i : connectedTail I i₀) :
    Nonempty
      ((etaleFundamentalGroupDiagram c xbar i₀ hconn).obj (OrderDual.toDual i) ≅
        etaleFundamentalGroup (D.obj (OrderDual.toDual i.1))
          (xbar.map (c.π.app (OrderDual.toDual i.1)))) := sorry

/-- The profinite fundamental-group diagram on a connected tail of a directed inverse
system of quasi-compact, quasi-separated schemes with affine transitions has a limit. -/
theorem etaleFundamentalGroupDiagram_hasLimit {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] {D : OrderDual I ⥤ Scheme.{u}} (c : Cone D)
    (xbar : GeometricPoint c.pt) (i₀ : I)
    (hconn : ∀ i : I, i₀ ≤ i → ConnectedSpace (D.obj i).carrier)
    [∀ j, CompactSpace (D.obj j).carrier]
    [∀ j, QuasiSeparatedSpace (D.obj j).carrier]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))] :
    HasLimit (etaleFundamentalGroupDiagram c xbar i₀ hconn) := sorry

/-- The inverse limit of the profinite fundamental-group diagram on a connected upper tail. -/
def etaleFundamentalGroupLimit {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] {D : OrderDual I ⥤ Scheme.{u}} (c : Cone D)
    (xbar : GeometricPoint c.pt) (i₀ : I)
    (hconn : ∀ i : I, i₀ ≤ i → ConnectedSpace (D.obj i).carrier)
    [∀ j, CompactSpace (D.obj j).carrier]
    [∀ j, QuasiSeparatedSpace (D.obj j).carrier]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))] :
    ProfiniteGrp :=
  @limit _ _ _ _ (etaleFundamentalGroupDiagram c xbar i₀ hconn)
    (etaleFundamentalGroupDiagram_hasLimit c xbar i₀ hconn)

/-- The étale fundamental group of a cone point maps compatibly to the
fundamental-group diagram on a connected upper tail. -/
def etaleFundamentalGroupLimitCone
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {D : OrderDual I ⥤ Scheme.{u}} (c : Cone D)
    (xbar : GeometricPoint c.pt) (i₀ : I)
    (hconn : ∀ i : I, i₀ ≤ i → ConnectedSpace (D.obj i).carrier)
    [∀ j, CompactSpace (D.obj j).carrier]
    [∀ j, QuasiSeparatedSpace (D.obj j).carrier]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))] :
    Cone (etaleFundamentalGroupDiagram c xbar i₀ hconn) where
  pt := etaleFundamentalGroup c.pt xbar
  π :=
    { app := fun i ↦
        ProfiniteGrp.ofHom
          ⟨((whiskeringLeft _ _ _).obj
            (finiteEtaleBaseChange (c.π.app (OrderDual.toDual i.1)))).mapAut
            xbar.finiteFiber, sorry⟩
      naturality := sorry }

/-- The canonical comparison from the étale fundamental group of a limit scheme to the
inverse limit of the fundamental-group diagram on a connected tail. -/
def fundamentalGroupLimitComparison
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j).carrier]
    [∀ j, QuasiSeparatedSpace (D.obj j).carrier]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (xbar : GeometricPoint c.pt) (i₀ : I)
    (hconn : ∀ i : I, i₀ ≤ i → ConnectedSpace (D.obj i).carrier) :
    etaleFundamentalGroup c.pt xbar ⟶
      etaleFundamentalGroupLimit c xbar i₀ hconn :=
  @limit.lift _ _ _ _ (etaleFundamentalGroupDiagram c xbar i₀ hconn)
    (etaleFundamentalGroupDiagram_hasLimit c xbar i₀ hconn)
    (etaleFundamentalGroupLimitCone c xbar i₀ hconn)

/-- For a directed inverse system of quasi-compact, quasi-separated schemes with affine
transitions and eventually connected stages, the canonical fundamental-group limit comparison
at a geometric point of the limit is an isomorphism. -/
theorem fundamentalGroup_limitIso
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j).carrier]
    [∀ j, QuasiSeparatedSpace (D.obj j).carrier]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (xbar : GeometricPoint c.pt) (i₀ : I)
    (hconn : ∀ i : I, i₀ ≤ i → ConnectedSpace (D.obj i).carrier) :
    IsIso (fundamentalGroupLimitComparison D c hc xbar i₀ hconn) := sorry

end AlgebraicGeometry.Scheme
