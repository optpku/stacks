/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Coproduct
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FreeQuotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-! # Free-quotient torsors of algebraic spaces -/

@[expose] public section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace
variable {S : Scheme.{u}}

/-- The graph of an action automorphism in the fibre product over its quotient. -/
def graphHom {W U : AlgebraicSpace S} {G : Type u} [Group G]
    (ρ : G →* Aut W) (q : W ⟶ U) (g : G) (h : (ρ g).hom ≫ q = q) :
    W ⟶ pullback q q :=
  pullback.lift ((ρ g).hom) (𝟙 W) (h.trans (Category.id_comp q).symm)

/-- The shear `(g, x) ↦ ((ρ g)·x, x)`, as the copairing of the graphs of
`(ρ g).hom`. -/
def shear {W U : AlgebraicSpace S} {G : Type u} [Group G]
    (ρ : G →* Aut W) (q : W ⟶ U) (h : ∀ g : G, (ρ g).hom ≫ q = q) :
    coproduct (fun _ : G ↦ W) ⟶ pullback q q :=
  coproductDesc fun g ↦ graphHom ρ q g (h g)

/-- The `g`-summand of the shear is the graph of `(ρ g).hom`. -/
theorem shear_ι {W U : AlgebraicSpace S} {G : Type u} [Group G]
    (ρ : G →* Aut W) (q : W ⟶ U) (h : ∀ g : G, (ρ g).hom ≫ q = q) (g : G) :
    coproductι (fun _ : G ↦ W) g ≫ shear ρ q h = graphHom ρ q g (h g) :=
  coproductι_desc (fun g ↦ graphHom ρ q g (h g)) g

/-- A morphism `q : W ⟶ U` is a free quotient morphism for `ρ : G →* Aut W`
when `q` is étale and surjective, the action of `G` lies over `U`, and the
shear `∐_{g : G} W ⟶ W ×_U W` is an isomorphism. -/
@[mk_iff]
class IsFreeQuotient {W U : AlgebraicSpace S} {G : Type u} [Group G]
    (ρ : G →* Aut W) (q : W ⟶ U) : Prop extends Etale q, Surjective q where
  /-- Each automorphism `(ρ g).hom` is a morphism over `U`. -/
  smul_comp : ∀ g : G, (ρ g).hom ≫ q = q
  /-- The shear `(g, x) ↦ ((ρ g)·x, x)` is an isomorphism onto `W ×_U W`. -/
  isIso_shear : IsIso (shear ρ q smul_comp)

/-- The shear of a free quotient morphism is an isomorphism. -/
instance instIsIso_shear {W U : AlgebraicSpace S} {G : Type u} [Group G]
    (ρ : G →* Aut W) (q : W ⟶ U) [h : IsFreeQuotient ρ q] :
    IsIso (shear ρ q h.smul_comp) :=
  h.isIso_shear

/-- The inverse of the identity shear for a subsingleton group, sending
`(x, x)` to the unique summand. -/
def shearSubsingletonInv {W : AlgebraicSpace S} {G : Type u} [Group G]
    [Subsingleton G] (_ρ : G →* Aut W) :
    pullback (𝟙 W) (𝟙 W) ⟶ coproduct fun _ : G ↦ W :=
  pullback.fst (𝟙 W) (𝟙 W) ≫ coproductι (fun _ : G ↦ W) 1

/-- The identity shear for a subsingleton group is an isomorphism
`∐_{g : G} W ≅ W ×_W W`. -/
noncomputable def shearSubsingletonIso {W : AlgebraicSpace S} {G : Type u}
    [Group G] [Subsingleton G] (ρ : G →* Aut W)
    (h : ∀ g : G, (ρ g).hom ≫ 𝟙 W = 𝟙 W) :
    coproduct (fun _ : G ↦ W) ≅ pullback (𝟙 W) (𝟙 W) where
  hom := shear ρ (𝟙 W) h
  inv := shearSubsingletonInv ρ
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The identity of `W` is a free quotient morphism for a subsingleton group:
the identity shear `W ≅ W ×_W W` is an isomorphism. -/
instance instIsFreeQuotient_subsingleton {W : AlgebraicSpace S} {G : Type u}
    [Group G] [Subsingleton G] (ρ : G →* Aut W) :
    IsFreeQuotient ρ (𝟙 W) :=
  let h : ∀ g : G, (ρ g).hom ≫ 𝟙 W = 𝟙 W := fun _ ↦ sorry
  { smul_comp := h
    isIso_shear := (shearSubsingletonIso ρ h).isIso_hom }

end AlgebraicGeometry.AlgebraicSpace
