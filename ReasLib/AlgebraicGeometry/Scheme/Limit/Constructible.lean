/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Topology.Constructible

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

namespace AlgebraicGeometry.Scheme.Limit

/-- If a locally constructible subset at one stage of a directed inverse system contains the
image of the limit, then it contains every transition image from all sufficiently large stages. -/
theorem exists_eventually_transition_mapsTo_of_isLocallyConstructible
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D)
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (hc : IsLimit c) (i : I) (E : Set (D.obj i))
    (hE : IsLocallyConstructible E)
    (hlimit : Set.MapsTo (c.π.app i) Set.univ E) :
    ∃ (i₀ : I) (hii₀ : i ≤ i₀), ∀ ⦃i' : I⦄, (hi₀i' : i₀ ≤ i') →
      Set.MapsTo
        (D.map (homOfLE (show OrderDual.toDual i' ≤ OrderDual.toDual i from
          (show i ≤ i' from le_trans hii₀ hi₀i'))))
        Set.univ E := sorry

end AlgebraicGeometry.Scheme.Limit
