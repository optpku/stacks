/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.EtaleNeighborhood

/-- The structural morphism of an étale neighbourhood and a morphism of base
schemes form the square inducing the map on fibres. -/
theorem fiberCommSq {X S : Scheme.{u}} (f : X ⟶ S) {x : X}
    (U : EtaleNeighborhood X x) :
    CommSq U.toEtale.hom (U.toEtale.hom ≫ f) f (𝟙 S) := sorry

/-- The selected point of an étale neighbourhood lies over the image point in
the composite fibre. -/
theorem fiberPoint_mem {X S : Scheme.{u}} (f : X ⟶ S) {x : X}
    (U : EtaleNeighborhood X x) :
    U.point ∈ (U.toEtale.hom ≫ f) ⁻¹' ({f x} : Set S) := sorry

/-- The selected point of the fibre of an étale neighbourhood. -/
noncomputable def fiberPoint {X S : Scheme.{u}} (f : X ⟶ S) {x : X}
    (U : EtaleNeighborhood X x) :
    (U.toEtale.hom ≫ f).fiber (f x) :=
  ((U.toEtale.hom ≫ f).fiberHomeo (f x)).symm
    ⟨U.point, fiberPoint_mem f U⟩

/-- The selected fibre point maps to the selected point of the original étale
neighbourhood. -/
theorem fiberPoint_fiberι {X S : Scheme.{u}} (f : X ⟶ S) {x : X}
    (U : EtaleNeighborhood X x) :
    (U.toEtale.hom ≫ f).fiberι (f x) (fiberPoint f U) = U.point := sorry

/-- The canonical map on fibres sends the selected fibre point to the selected
point of the fibre of the base morphism. -/
theorem fiberMap_fiberPoint {X S : Scheme.{u}} (f : X ⟶ S) {x : X}
    (U : EtaleNeighborhood X x) :
    Scheme.Hom.fiberMap (U.toEtale.hom ≫ f) U.toEtale.hom (𝟙 S) f
        (fiberCommSq f U) (f x) (fiberPoint f U) =
      f.asFiber x := sorry

/-- The canonical pointed étale neighbourhood on the fibre obtained from an
étale neighbourhood of the original scheme. -/
noncomputable def fiber {X S : Scheme.{u}} (f : X ⟶ S) {x : X}
    (U : EtaleNeighborhood X x) :
    EtaleNeighborhood (f.fiber (f x)) (f.asFiber x) :=
  EtaleNeighborhood.of
    (@Scheme.Etale.mk _ _
      (Scheme.Hom.fiberMap (U.toEtale.hom ≫ f) U.toEtale.hom (𝟙 S) f
        (fiberCommSq f U) (f x))
      (@Scheme.Hom.fiberMap_etale _ _ _ _ (U.toEtale.hom ≫ f)
        U.toEtale.hom (𝟙 S) f U.toEtale.prop inferInstance
        (fiberCommSq f U) (f x)))
    (fiberPoint f U) (fiberMap_fiberPoint f U)

/-- The carrier of the fibre étale neighbourhood is the fibre of the composite
structural morphism. -/
theorem fiber_toEtale_left {X S : Scheme.{u}} (f : X ⟶ S) {x : X}
    (U : EtaleNeighborhood X x) :
    (fiber f U).toEtale.left = (U.toEtale.hom ≫ f).fiber (f x) := sorry

/-- The selected point and structural map of the fibre neighbourhood are
compatible with the canonical projections to `U.toEtale.left` and `X`. -/
theorem fiber_spec {X S : Scheme.{u}} (f : X ⟶ S) {x : X}
    (U : EtaleNeighborhood X x) :
    (U.toEtale.hom ≫ f).fiberι (f x)
        (eqToHom (fiber_toEtale_left f U) (fiber f U).point) = U.point ∧
      (fiber f U).toEtale.hom ≫ f.fiberι (f x) =
        eqToHom (fiber_toEtale_left f U) ≫
          (U.toEtale.hom ≫ f).fiberι (f x) ≫ U.toEtale.hom := sorry

/-- Every étale neighbourhood of the distinguished point in a fibre is
dominated, by an open immersion of pointed étale neighbourhoods, by the fibre
of an étale neighbourhood of the original point. -/
@[stacks 0CAS]
theorem exists_fiberOpenImmersion {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (V : EtaleNeighborhood (f.fiber (f x)) (f.asFiber x)) :
    ∃ (U : EtaleNeighborhood X x) (h : Hom (fiber f U) V),
      IsOpenImmersion h.toEtaleHom.left := sorry

end AlgebraicGeometry.Scheme.EtaleNeighborhood
