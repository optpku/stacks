/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DirectedAffine.Limit
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DirectedAffine.Comparison

/-!
# Fibre products along projections of directed affine limits

The tail diagrams `i' ↦ X_{i'} ×_{X_i} T` and the identification of
`X ×_{X_i} T` with their inverse limit.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits (HasLimit Cone IsLimit)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DirectedAffine

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
variable (i : I) {T : AlgebraicSpace S} (g : T ⟶ D.obj (OrderDual.toDual i))

/-- Compatibility of a later-to-earlier transition with the two maps to the
base stage in the tail fibre-product diagram. -/
theorem pullbackTail_map_fst_w {j k : OrderDual (Tail i)} (f : j ⟶ k) :
    D.map (homOfLE j.2) ≫ 𝟙 (D.obj (OrderDual.toDual i)) =
      D.map (homOfLE (leOfHom f)) ≫ D.map (homOfLE k.2) :=
  sorry

/-- The identity on `T` is compatible with the two copies of `g` in the
defining squares of `pullbackTail`. -/
theorem pullbackTail_map_snd_w {j k : OrderDual (Tail i)} (f : j ⟶ k) :
    g ≫ 𝟙 (D.obj (OrderDual.toDual i)) = 𝟙 T ≫ g :=
  sorry

/-- The induced map `X_{j} ×_{X_i} T ⟶ X_{k} ×_{X_i} T` of a later-to-earlier
transition in the tail. -/
def pullbackTailMap {j k : OrderDual (Tail i)} (f : j ⟶ k) :
    Limits.pullback (D.map (homOfLE j.2)) g ⟶ Limits.pullback (D.map (homOfLE k.2)) g :=
  let e1 := pullbackTail_map_fst_w D i f
  let e2 := pullbackTail_map_snd_w D i g f
  CategoryTheory.Limits.pullback.map
    (D.map (homOfLE j.2)) g (D.map (homOfLE k.2)) g
    (D.map (homOfLE (leOfHom f))) (𝟙 T) (𝟙 (D.obj (OrderDual.toDual i))) e1 e2

/-- Identity morphisms of the tail fibre-product diagram are identity
morphisms of algebraic spaces. -/
theorem pullbackTailMap_id (j : OrderDual (Tail i)) :
    pullbackTailMap D i g (𝟙 j) = 𝟙 (Limits.pullback (D.map (homOfLE j.2)) g) :=
  sorry

/-- Composition of morphisms of the tail fibre-product diagram is composition
of the induced maps of fibre products. -/
theorem pullbackTailMap_comp {j k l : OrderDual (Tail i)} (f : j ⟶ k) (h : k ⟶ l) :
    pullbackTailMap D i g (f ≫ h) = pullbackTailMap D i g f ≫ pullbackTailMap D i g h :=
  sorry

/-- The directed diagram of fibre products `X_{i'} ×_{X_i} T` for `i' ≥ i`. -/
def pullbackTail : OrderDual (Tail i) ⥤ AlgebraicSpace S where
  obj j := Limits.pullback (D.map (homOfLE j.2)) g
  map f := pullbackTailMap D i g f
  map_id := pullbackTailMap_id D i g
  map_comp := pullbackTailMap_comp D i g

/-- The object of `pullbackTail` at a tail index is the fibre product of the
corresponding transition with `g`. -/
theorem pullbackTail_obj (j : Tail i) :
    (pullbackTail D i g).obj (OrderDual.toDual j) = Limits.pullback (D.map (homOfLE j.2)) g :=
  sorry

/-- Transition maps of `pullbackTail` are the induced maps of fibre products. -/
theorem pullbackTail_map {j k : OrderDual (Tail i)} (f : j ⟶ k) :
    (pullbackTail D i g).map f = pullbackTailMap D i g f :=
  sorry

/-- Transition maps of the tail fibre-product diagram are affine. -/
instance affine_pullbackTail_map {j j' : Tail i} (h : j ≤ j') :
    Affine ((pullbackTail D i g).map (homOfLE h)) :=
  sorry

/-- Compatibility of a limit projection with the transition to the base stage. -/
theorem pullbackCone_π_fst_w (j : OrderDual (Tail i)) :
    Limits.limit.π D (OrderDual.toDual i) ≫ 𝟙 (D.obj (OrderDual.toDual i)) =
      Limits.limit.π D (OrderDual.toDual j.1) ≫ D.map (homOfLE j.2) :=
  sorry

/-- The identity on `T` is compatible with the two copies of `g` in the
defining squares of `pullbackCone`. -/
theorem pullbackCone_π_snd_w (j : OrderDual (Tail i)) :
    g ≫ 𝟙 (D.obj (OrderDual.toDual i)) = 𝟙 T ≫ g :=
  sorry

/-- The cone projection `X ×_{X_i} T ⟶ X_{i'} ×_{X_i} T`. -/
def pullbackCone_π_app (j : OrderDual (Tail i)) :
    Limits.pullback (Limits.limit.π D (OrderDual.toDual i)) g ⟶
      Limits.pullback (D.map (homOfLE j.2)) g :=
  let e1 := pullbackCone_π_fst_w D i j
  let e2 := pullbackCone_π_snd_w D i g j
  CategoryTheory.Limits.pullback.map
    (Limits.limit.π D (OrderDual.toDual i)) g (D.map (homOfLE j.2)) g
    (Limits.limit.π D (OrderDual.toDual j.1)) (𝟙 T) (𝟙 (D.obj (OrderDual.toDual i))) e1 e2

/-- Naturality of `pullbackCone_π_app`. -/
theorem pullbackCone_π_naturality ⦃j k : OrderDual (Tail i)⦄ (f : j ⟶ k) :
    ((Functor.const (OrderDual (Tail i))).obj
          (Limits.pullback (Limits.limit.π D (OrderDual.toDual i)) g)).map f ≫
        pullbackCone_π_app D i g k =
      pullbackCone_π_app D i g j ≫ pullbackTailMap D i g f :=
  sorry

/-- The fibre product `X ×_{X_i} T` as a cone over the tail diagram
`i' ↦ X_{i'} ×_{X_i} T`. -/
def pullbackCone : Cone (pullbackTail D i g) where
  pt := Limits.pullback (Limits.limit.π D (OrderDual.toDual i)) g
  π :=
    { app := pullbackCone_π_app D i g
      naturality := pullbackCone_π_naturality D i g }

/-- A cofinal bound of the base stage and an arbitrary index, as a tail object. -/
def coneToD_bound (k : OrderDual I) : Tail i :=
  ⟨directedBound i (OrderDual.ofDual k), directedBound_le_left i (OrderDual.ofDual k)⟩

/-- The component at `k` of the cone from a tail fibre-product cone to `D`. -/
def coneToD_π_app (s : Cone (pullbackTail D i g)) (k : OrderDual I) : s.pt ⟶ D.obj k :=
  s.π.app (OrderDual.toDual (coneToD_bound i k)) ≫
    Limits.pullback.fst (D.map (homOfLE (coneToD_bound i k).2)) g ≫
      D.map (homOfLE (directedBound_le_right i (OrderDual.ofDual k)))

/-- Naturality of `coneToD_π_app`. -/
theorem coneToD_π_naturality (s : Cone (pullbackTail D i g)) ⦃k k' : OrderDual I⦄ (f : k ⟶ k') :
    ((Functor.const (OrderDual I)).obj s.pt).map f ≫ coneToD_π_app D i g s k' =
      coneToD_π_app D i g s k ≫ D.map f :=
  sorry

/-- The cone over `D` obtained by extending a cone over the tail fibre products. -/
def coneToD (s : Cone (pullbackTail D i g)) : Cone D where
  pt := s.pt
  π :=
    { app := coneToD_π_app D i g s
      naturality := coneToD_π_naturality D i g s }

/-- The second factor of the mediating morphism into `X ×_{X_i} T`. -/
def pullbackCone_lift_snd (s : Cone (pullbackTail D i g)) : s.pt ⟶ T :=
  s.π.app (OrderDual.toDual ⟨i, le_rfl⟩) ≫
    Limits.pullback.snd (D.map (homOfLE (le_rfl : i ≤ i))) g

/-- The mediating square for `pullbackCone_lift` commutes. -/
theorem pullbackCone_lift_w (s : Cone (pullbackTail D i g)) :
    Limits.limit.lift D (coneToD D i g s) ≫ Limits.limit.π D (OrderDual.toDual i) =
      pullbackCone_lift_snd D i g s ≫ g :=
  sorry

/-- The mediating morphism into `X ×_{X_i} T` induced by a cone over the tail
fibre products. -/
def pullbackCone_lift (s : Cone (pullbackTail D i g)) : s.pt ⟶ (pullbackCone D i g).pt :=
  Limits.pullback.lift (Limits.limit.lift D (coneToD D i g s)) (pullbackCone_lift_snd D i g s)
    (pullbackCone_lift_w D i g s)

/-- The mediating morphism recovers the given tail cone projection. -/
theorem pullbackCone_lift_fac (s : Cone (pullbackTail D i g)) (j : OrderDual (Tail i)) :
    pullbackCone_lift D i g s ≫ (pullbackCone D i g).π.app j = s.π.app j :=
  sorry

/-- The mediating morphism is the unique cone morphism to `pullbackCone`. -/
theorem pullbackCone_lift_uniq (s : Cone (pullbackTail D i g)) (m : s.pt ⟶ (pullbackCone D i g).pt)
    (w : ∀ j, m ≫ (pullbackCone D i g).π.app j = s.π.app j) :
    m = pullbackCone_lift D i g s :=
  sorry

/-- The fibre product `X ×_{X_i} T` is an inverse limit of the tail diagram
`i' ↦ X_{i'} ×_{X_i} T`. -/
def isLimit_pullbackCone : IsLimit (pullbackCone D i g) where
  lift := pullbackCone_lift D i g
  fac := pullbackCone_lift_fac D i g
  uniq := pullbackCone_lift_uniq D i g

/-- The comparison morphism from the fibre product `X ×_{X_i} T` to the explicitly
constructed inverse limit of the tail fibre products. -/
def pullback_π_hom :
    Limits.pullback (Limits.limit.π D (OrderDual.toDual i)) g ⟶
      AlgebraicGeometry.AlgebraicSpace.DirectedAffine.limit (pullbackTail D i g) :=
  limitCone_lift (pullbackTail D i g) (pullbackCone D i g)

/-- The comparison morphism from the explicitly constructed inverse limit of the
tail fibre products to the fibre product `X ×_{X_i} T`. -/
def pullback_π_inv :
    AlgebraicGeometry.AlgebraicSpace.DirectedAffine.limit (pullbackTail D i g) ⟶
      Limits.pullback (Limits.limit.π D (OrderDual.toDual i)) g :=
  pullbackCone_lift D i g (limitCone (pullbackTail D i g))

/-- The two comparison morphisms are inverse. -/
theorem pullback_π_hom_inv_id : pullback_π_hom D i g ≫ pullback_π_inv D i g = 𝟙 _ :=
  sorry

/-- The two comparison morphisms are inverse. -/
theorem pullback_π_inv_hom_id : pullback_π_inv D i g ≫ pullback_π_hom D i g = 𝟙 _ :=
  sorry

/-- The fibre product `X ×_{X_i} T` is isomorphic to the explicitly constructed
inverse limit of the tail fibre products. -/
def pullback_π_iso :
    Limits.pullback (Limits.limit.π D (OrderDual.toDual i)) g ≅
      AlgebraicGeometry.AlgebraicSpace.DirectedAffine.limit (pullbackTail D i g) where
  hom := pullback_π_hom D i g
  inv := pullback_π_inv D i g
  hom_inv_id := pullback_π_hom_inv_id D i g
  inv_hom_id := pullback_π_inv_hom_id D i g

end AlgebraicGeometry.AlgebraicSpace.DirectedAffine
