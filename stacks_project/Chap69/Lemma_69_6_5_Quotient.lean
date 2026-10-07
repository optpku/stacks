module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap65.Lemma_65_8_4_Coproduct
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap66.Lemma_66_34_1_Quotient
public import stacks_project.Chap67.Definition_67_5_2_Surjective

/-!
# Free quotient morphisms of algebraic spaces

A morphism `q : W ⟶ U` is a free quotient morphism for a free action
`ρ : G →* Aut W` when `q` is étale and surjective, each automorphism
`(ρ g).hom` lies over `U`, and the shear `(g, x) ↦ ((ρ g)·x, x)` is an
isomorphism `∐_{g : G} W ≅ W ×_U W`. This is the source-facing interface
for `U = W/G` without constructing an algebraic space from the
universe-raised fppf quotient sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- An isomorphism of algebraic spaces is étale. -/
instance instEtale_isIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIso f] :
    Etale f := sorry

/-- Automorphisms of an algebraic space are étale. -/
instance instEtale_aut {W : AlgebraicSpace S} {G : Type u} [Group G]
    (ρ : G →* Aut W) (g : G) : Etale (ρ g).hom :=
  inferInstance

/-- The coproduct of copies of `W` indexed by `G`. -/
def actionCoproduct {W : AlgebraicSpace S} {G : Type u} [Group G]
    (_ρ : G →* Aut W) : AlgebraicSpace S :=
  coproduct fun _ : G ↦ W

/-- The graph of `(ρ g).hom` as a morphism `W ⟶ W ×_U W`, using that
`(ρ g).hom` lies over `U`. -/
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
