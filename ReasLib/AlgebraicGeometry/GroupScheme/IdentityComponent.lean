/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.Connected
public import ReasLib.AlgebraicGeometry.GroupScheme.GeometricallyIrreducible
public import ReasLib.AlgebraicGeometry.GroupScheme.QuasiCompact
public import ReasLib.AlgebraicGeometry.GroupScheme.Subgroup.Factorization
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.ConnectedComponent

/-!
# The identity component of a group scheme

This file constructs the canonical closed subgroup scheme supported on the connected component
of the identity of a group scheme over a field.
-/

@[expose] public section

open CategoryTheory MonoidalCategory MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupScheme

variable {k : Type u} [Field k]

namespace IdentityComponent

/-- The connected component of the identity point, as a point of `ConnectedComponents`. -/
def component (G : SchemeOverField k) [GrpObj G] : ConnectedComponents G.left :=
  (η[G].left (IsLocalRing.closedPoint k) : ConnectedComponents G.left)

/-- The canonical flat ideal-sheaf datum supported on the connected component of the
identity. -/
def ideal (G : SchemeOverField k) [GrpObj G] : G.left.IdealSheafData :=
  G.left.connectedComponentIdeal (component G)

/-- The identity-component closed immersion is flat. -/
theorem flat_ideal (G : SchemeOverField k) [GrpObj G] : Flat (ideal G).subschemeι :=
  G.left.flat_connectedComponentIdeal (component G)

/-- The support of the identity-component ideal sheaf is the connected component of the
identity. -/
theorem support_ideal (G : SchemeOverField k) [GrpObj G] :
    ((ideal G).support : Set G.left) =
      connectedComponent (η[G].left (IsLocalRing.closedPoint k)) :=
  G.left.support_connectedComponentIdeal (component G)

/-- The selected ideal-sheaf datum is flat and has support the connected component of the
identity. -/
theorem ideal_spec (G : SchemeOverField k) [GrpObj G] :
    Flat (ideal G).subschemeι ∧
      ((ideal G).support : Set G.left) =
        connectedComponent (η[G].left (IsLocalRing.closedPoint k)) :=
  ⟨flat_ideal G, support_ideal G⟩

/-- A flat ideal-sheaf datum supported on the identity component is the selected datum. -/
theorem ideal_unique (G : SchemeOverField k) [GrpObj G]
    (I : G.left.IdealSheafData) (hI : Flat I.subschemeι)
    (h_support : (I.support : Set G.left) =
      connectedComponent (η[G].left (IsLocalRing.closedPoint k))) :
    I = ideal G :=
  G.left.eq_connectedComponentIdeal (component G) I hI h_support

/-- The identity-component closed subscheme, regarded as a scheme over the base field. -/
def source (G : SchemeOverField k) [GrpObj G] : SchemeOverField k :=
  Over.mk ((ideal G).subschemeι ≫ G.hom)

/-- The structural morphism of `source G` is the composite through `G`. -/
theorem source_hom (G : SchemeOverField k) [GrpObj G] :
    (source G).hom = (ideal G).subschemeι ≫ G.hom := rfl

/-- The closed-subscheme inclusion of the identity component in `G`. -/
def inclusion (G : SchemeOverField k) [GrpObj G] : source G ⟶ G :=
  Over.homMk (ideal G).subschemeι

/-- The underlying scheme morphism of the identity-component inclusion is the canonical
closed-subscheme immersion. -/
theorem inclusion_left (G : SchemeOverField k) [GrpObj G] :
    (inclusion G).left = (ideal G).subschemeι := rfl

/-- The identity-component inclusion is a closed immersion on underlying schemes. -/
instance instIsClosedImmersionInclusion (G : SchemeOverField k) [GrpObj G] :
    IsClosedImmersion (inclusion G).left := by
  change IsClosedImmersion (ideal G).subschemeι
  infer_instance

/-- The identity-component inclusion is a monomorphism in the over category. -/
instance instMonoInclusion (G : SchemeOverField k) [GrpObj G] : Mono (inclusion G) :=
  Over.mono_of_mono_left (inclusion G)

/-- The image of the unit lies in the identity component. -/
theorem one_range_subset (G : SchemeOverField k) [GrpObj G] :
    Set.range η[G].left ⊆ ((ideal G).support : Set G.left) := sorry

/-- The explicit lift of the unit map through the flat closed identity-component subscheme. -/
def oneLeft (G : SchemeOverField k) [GrpObj G] :
    (𝟙_ (SchemeOverField k)).left ⟶ (source G).left :=
  (ideal G).flatLift (flat_ideal G) η[G].left (one_range_subset G)

/-- The underlying lifted unit map is a morphism over the base field. -/
theorem oneLeft_over (G : SchemeOverField k) [GrpObj G] :
    oneLeft G ≫ (source G).hom = (𝟙_ (SchemeOverField k)).hom := sorry

/-- The canonical lift of the group unit to the identity component. -/
def one (G : SchemeOverField k) [GrpObj G] :
    𝟙_ (SchemeOverField k) ⟶ source G :=
  Over.homMk (oneLeft G) (oneLeft_over G)

/-- The lifted unit followed by the inclusion is the unit of `G`. -/
theorem one_comp_inclusion (G : SchemeOverField k) [GrpObj G] :
    one G ≫ inclusion G = η[G] := sorry

/-- A lift of the unit through the identity component equals the canonical lift. -/
theorem one_unique (G : SchemeOverField k) [GrpObj G]
    (e : 𝟙_ (SchemeOverField k) ⟶ source G) (he : e ≫ inclusion G = η[G]) :
    e = one G := sorry

/-- Restricted multiplication has image in the identity component. -/
theorem mul_range_subset (G : SchemeOverField k) [GrpObj G] :
    Set.range (((inclusion G ⊗ₘ inclusion G) ≫ μ[G]).left) ⊆
      ((ideal G).support : Set G.left) := sorry

/-- The explicit lift of restricted multiplication through the flat closed identity-component
subscheme. -/
def mulLeft (G : SchemeOverField k) [GrpObj G] :
    (source G ⊗ source G).left ⟶ (source G).left :=
  (ideal G).flatLift (flat_ideal G) (((inclusion G ⊗ₘ inclusion G) ≫ μ[G]).left)
    (mul_range_subset G)

/-- The underlying lifted multiplication is a morphism over the base field. -/
theorem mulLeft_over (G : SchemeOverField k) [GrpObj G] :
    mulLeft G ≫ (source G).hom = (source G ⊗ source G).hom := sorry

/-- The canonical multiplication on the identity component. -/
def mul (G : SchemeOverField k) [GrpObj G] :
    source G ⊗ source G ⟶ source G :=
  Over.homMk (mulLeft G) (mulLeft_over G)

/-- The lifted multiplication followed by the inclusion is the restricted multiplication of
`G`. -/
theorem mul_comp_inclusion (G : SchemeOverField k) [GrpObj G] :
    mul G ≫ inclusion G = (inclusion G ⊗ₘ inclusion G) ≫ μ[G] := sorry

/-- A lift of multiplication through the identity component equals the canonical lift. -/
theorem mul_unique (G : SchemeOverField k) [GrpObj G]
    (m : source G ⊗ source G ⟶ source G)
    (hm : m ≫ inclusion G = (inclusion G ⊗ₘ inclusion G) ≫ μ[G]) :
    m = mul G := sorry

/-- Restricted inversion has image in the identity component. -/
theorem inv_range_subset (G : SchemeOverField k) [GrpObj G] :
    Set.range ((inclusion G ≫ ι[G]).left) ⊆ ((ideal G).support : Set G.left) := sorry

/-- The explicit lift of restricted inversion through the flat closed identity-component
subscheme. -/
def invLeft (G : SchemeOverField k) [GrpObj G] : (source G).left ⟶ (source G).left :=
  (ideal G).flatLift (flat_ideal G) ((inclusion G ≫ ι[G]).left) (inv_range_subset G)

/-- The underlying lifted inverse is a morphism over the base field. -/
theorem invLeft_over (G : SchemeOverField k) [GrpObj G] :
    invLeft G ≫ (source G).hom = (source G).hom := sorry

/-- The canonical inversion on the identity component. -/
def inv (G : SchemeOverField k) [GrpObj G] : source G ⟶ source G :=
  Over.homMk (invLeft G) (invLeft_over G)

/-- The lifted inverse followed by the inclusion is inversion restricted from `G`. -/
theorem inv_comp_inclusion (G : SchemeOverField k) [GrpObj G] :
    inv G ≫ inclusion G = inclusion G ≫ ι[G] := sorry

/-- A lift of inversion through the identity component equals the canonical lift. -/
theorem inv_unique (G : SchemeOverField k) [GrpObj G] (i : source G ⟶ source G)
    (hi : i ≫ inclusion G = inclusion G ≫ ι[G]) : i = inv G := sorry

/-- The unit, multiplication, and inverse factorizations defining the identity subgroup. -/
noncomputable def factorization (G : SchemeOverField k) [GrpObj G] :
    GrpObj.Factorization (inclusion G) where
  one := one G
  mul := mul G
  inv := inv G
  one_hom := one_comp_inclusion G
  mul_hom := mul_comp_inclusion G
  inv_hom := inv_comp_inclusion G

/-- The unit map stored by the identity-component factorization is the canonical lift. -/
theorem factorization_one (G : SchemeOverField k) [GrpObj G] :
    (factorization G).one = one G := sorry

/-- The multiplication stored by the identity-component factorization is the canonical lift. -/
theorem factorization_mul (G : SchemeOverField k) [GrpObj G] :
    (factorization G).mul = mul G := sorry

/-- The inverse stored by the identity-component factorization is the canonical lift. -/
theorem factorization_inv (G : SchemeOverField k) [GrpObj G] :
    (factorization G).inv = inv G := sorry

end IdentityComponent

/-- The canonical closed subgroup scheme supported on the connected component of the identity. -/
noncomputable def identityComponent (G : SchemeOverField k) [GrpObj G] :
    Scheme.ClosedSubgroup G :=
  (IdentityComponent.factorization G).toClosedSubgroup

/-- The underlying inclusion of `identityComponent G` has range the connected component of the
identity point. -/
theorem range_identityComponent (G : SchemeOverField k) [GrpObj G] :
    Set.range (identityComponent G).inclusion.left =
      connectedComponent (η[G].left (IsLocalRing.closedPoint k)) := sorry

/-- The inclusion of the identity-component subgroup is flat. -/
instance instFlatIdentityComponent (G : SchemeOverField k) [GrpObj G] :
    Flat (identityComponent G).inclusion.left := sorry

/-- The identity-component subgroup has connected underlying space. -/
instance instConnectedSpaceIdentityComponent (G : SchemeOverField k) [GrpObj G] :
    ConnectedSpace (identityComponent G).left.X.left := sorry

/-- The identity-component subgroup is geometrically irreducible over the base field. -/
instance instGeometricallyIrreducibleIdentityComponent
    (G : SchemeOverField k) [GrpObj G] :
    GeometricallyIrreducible (identityComponent G).left.X.hom := sorry

/-- The identity-component subgroup has quasi-compact underlying space. -/
instance instCompactSpaceIdentityComponent (G : SchemeOverField k) [GrpObj G] :
    CompactSpace (identityComponent G).left.X.left := sorry

end AlgebraicGeometry.GroupScheme
