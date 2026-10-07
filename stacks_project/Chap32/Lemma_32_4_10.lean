module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Constructible
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Topology

universe u

/- Lemma 32.4.10: a locally constructible subset at one stage that contains the image of the
limit contains the transition images from all sufficiently large stages. -/
@[stacks 05F4] #check
  (AlgebraicGeometry.Scheme.Limit.exists_eventually_transition_mapsTo_of_isLocallyConstructible :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D)
      [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
      (hc : IsLimit c) (i : I) (E : Set (D.obj i)),
      IsLocallyConstructible E → Set.MapsTo (c.π.app i) Set.univ E →
        ∃ (i₀ : I) (hii₀ : i ≤ i₀), ∀ ⦃i' : I⦄, (hi₀i' : i₀ ≤ i') →
          Set.MapsTo
            (D.map (homOfLE (show OrderDual.toDual i' ≤ OrderDual.toDual i from
              (show i ≤ i' from le_trans hii₀ hi₀i'))))
            Set.univ E)
