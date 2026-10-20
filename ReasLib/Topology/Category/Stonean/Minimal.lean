module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.Category.Stonean.Lift
public import ReasLib.Topology.ExtremallyDisconnected.Maps
public import ReasLib.Topology.Maps.Minimal

/-!
# Minimal Stonean covers

This module bundles a Stonean cover together with its minimal-surjectivity condition.  The bundle
keeps the cover map, its domain, and its minimality proof coherent, while comparison maps remain
the canonical `CompHaus.lift` maps supplied by projectivity.
-/

@[expose] public section

universe u

open CategoryTheory Function

namespace CompHaus

/-- A Stonean cover of a compact Hausdorff space that is minimal among closed subspaces of its
source still mapping onto the base. -/
@[stacks 090D "minimal Stonean covers"]
structure MinimalStoneanCover (X : CompHaus.{u}) where
  /-- The Stonean covering space. -/
  space : Stonean.{u}
  /-- The map from the covering space to the base. -/
  π : space.compHaus ⟶ X
  /-- The cover is minimal as a surjection. -/
  minimal : IsMinimalSurjective π

namespace MinimalStoneanCover

variable {X : CompHaus.{u}}

/-- The canonical comparison lift between two minimal Stonean covers of the same base. -/
@[stacks 090D "comparison lift of minimal Stonean covers"]
noncomputable def lift (A B : MinimalStoneanCover X) :
    A.space.compHaus ⟶ B.space.compHaus :=
  CompHaus.liftOfSurjective A.π B.π B.minimal.surjective

/-- The comparison lift lies over the common base. -/
@[reassoc]
theorem lift_fac (A B : MinimalStoneanCover X) :
    lift A B ≫ B.π = A.π := sorry

/-- The comparison lift from `A` to `B` is inverted by the comparison lift from `B` to `A`. -/
theorem lift_leftInverse (A B : MinimalStoneanCover X) :
    Function.LeftInverse (lift B A) (lift A B) := sorry

/-- The comparison lift from `A` to `B` has the reverse comparison lift as a right inverse. -/
theorem lift_rightInverse (A B : MinimalStoneanCover X) :
    Function.RightInverse (lift B A) (lift A B) := sorry

/-- The canonical homeomorphism between two minimal Stonean covers of the same base. -/
@[stacks 090D "canonical comparison of minimal Stonean covers"]
noncomputable def homeomorph (A B : MinimalStoneanCover X) : A.space ≃ₜ B.space where
  toEquiv :=
    { toFun := lift A B
      invFun := lift B A
      left_inv := lift_leftInverse A B
      right_inv := lift_rightInverse A B }
  continuous_toFun := (lift A B).hom.hom.continuous
  continuous_invFun := (lift B A).hom.hom.continuous

/-- The canonical comparison homeomorphism is the chosen projective lift. -/
@[simp]
theorem homeomorph_apply (A B : MinimalStoneanCover X) (a : A.space) :
    homeomorph A B a = lift A B a := sorry

/-- The canonical comparison homeomorphism commutes with the maps to the common base. -/
theorem homeomorph_over (A B : MinimalStoneanCover X) :
    B.π ∘ homeomorph A B = A.π := sorry

/-- The canonical comparison of minimal Stonean covers as an isomorphism in `Stonean`. -/
@[stacks 090D "comparison isomorphism of minimal Stonean covers"]
noncomputable def stoneanIso (A B : MinimalStoneanCover X) : A.space ≅ B.space :=
  CompHausLike.isoOfHomeo (homeomorph A B)

/-- The underlying compact-Hausdorff hom of `stoneanIso` is the chosen Stonean lift. -/
@[simp]
theorem stoneanIso_hom (A B : MinimalStoneanCover X) :
    Stonean.toCompHaus.map (stoneanIso A B).hom = lift A B := sorry

/-- The underlying compact-Hausdorff hom of `stoneanIso` has the expected value on points. -/
@[simp]
theorem stoneanIso_hom_apply (A B : MinimalStoneanCover X) (a : A.space) :
    Stonean.toCompHaus.map (stoneanIso A B).hom a = lift A B a := sorry

/-- The categorical comparison in `Stonean` commutes with the maps to the common base. -/
@[reassoc]
theorem stoneanIso_hom_fac (A B : MinimalStoneanCover X) :
    Stonean.toCompHaus.map (stoneanIso A B).hom ≫ B.π = A.π := sorry

/-- The `CompHaus` image of the canonical categorical comparison in `Stonean`. -/
noncomputable def iso (A B : MinimalStoneanCover X) :
    A.space.compHaus ≅ B.space.compHaus :=
  Stonean.toCompHaus.mapIso (stoneanIso A B)

/-- The hom of the compact-Hausdorff comparison isomorphism is the chosen Stonean lift. -/
@[simp]
theorem iso_hom (A B : MinimalStoneanCover X) :
    (iso A B).hom = lift A B := sorry

/-- The categorical comparison isomorphism commutes with the maps to the common base. -/
@[reassoc]
theorem iso_hom_fac (A B : MinimalStoneanCover X) :
    (iso A B).hom ≫ B.π = A.π := sorry

/-- A minimal Stonean cover satisfies the double-power cardinal bound induced by the dense
canonical section of its cover map. -/
@[stacks 090E "cardinality bound for minimal Stonean covers"]
theorem cardinalMk_le_doublePower (A : MinimalStoneanCover X)
    (κ : Cardinal.{u}) (hκX : Cardinal.mk X ≤ κ) :
    Cardinal.mk A.space ≤ (2 : Cardinal) ^ ((2 : Cardinal) ^ κ) := sorry

end MinimalStoneanCover

end CompHaus
