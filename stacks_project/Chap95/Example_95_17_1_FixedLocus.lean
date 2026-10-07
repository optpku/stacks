module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_9_1
public import stacks_project.Chap66.Definition_66_4_1_Points

/-!
# Scheme-theoretic fixed loci of abstract group automorphisms

The fibre product `X^g` of the diagonal `(1, 1)` with the graph `(g, 1)`, the residual
action of a commutative group, and the passage from scheme automorphisms to algebraic-space
automorphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.QuotientStack.FixedLocus

/-- Binary products of schemes over `S` are fibre products over `S`. -/
instance hasBinaryProducts_over (S : Scheme.{u}) : HasBinaryProducts (Over S) :=
  Over.ConstructProducts.over_binaryProduct_of_pullback

/-- The diagonal morphism `(1, 1) : X ⟶ X ×_S X`. -/
def diagonal {S : Scheme.{u}} (X : Over S) : X ⟶ X ⨯ X :=
  prod.lift (𝟙 X) (𝟙 X)

/-- The graph morphism `(g, 1) : X ⟶ X ×_S X` of an automorphism. -/
def graph {S : Scheme.{u}} {G : Type u} [Group G] {X : Over S}
    (ρ : G →* Aut X) (g : G) : X ⟶ X ⨯ X :=
  prod.lift (ρ g).hom (𝟙 X)

/-- The scheme-theoretic fixed locus `X^g`, realised as the fibre product of `(1, 1)` with
`(g, 1)`. -/
def fixedLocus {S : Scheme.{u}} {G : Type u} [Group G] {X : Over S}
    (ρ : G →* Aut X) (g : G) : Over S :=
  pullback (diagonal X) (graph ρ g)

/-- The closed immersion `X^g ⟶ X` given by the first pullback projection. -/
def inclusion {S : Scheme.{u}} {G : Type u} [Group G] {X : Over S}
    (ρ : G →* Aut X) (g : G) : fixedLocus ρ g ⟶ X :=
  pullback.fst (diagonal X) (graph ρ g)

/-- The two pullback legs of `X^g` to `X` coincide. -/
theorem fixedLocus_fst_eq_snd {S : Scheme.{u}} {G : Type u} [Group G] {X : Over S}
    (ρ : G →* Aut X) (g : G) :
    pullback.fst (diagonal X) (graph ρ g) = pullback.snd (diagonal X) (graph ρ g) :=
  sorry

/-- The inclusion of `X^g` equalizes `ρ g` and the identity. -/
theorem inclusion_spec {S : Scheme.{u}} {G : Type u} [Group G] {X : Over S}
    (ρ : G →* Aut X) (g : G) :
    inclusion ρ g ≫ (ρ g).hom = inclusion ρ g :=
  sorry

/-- The pullback condition identifying `X^g` as the fibre product of `(1, 1)` with `(g, 1)`. -/
theorem fixedLocus_condition {S : Scheme.{u}} {G : Type u} [Group G] {X : Over S}
    (ρ : G →* Aut X) (g : G) :
    inclusion ρ g ≫ diagonal X = inclusion ρ g ≫ graph ρ g :=
  sorry

/-- Swapping the cospan legs presents `X^g` as the fibre product of `(g, 1)` against `(1, 1)`. -/
def equalizerIso {S : Scheme.{u}} {G : Type u} [Group G] {X : Over S}
    (ρ : G →* Aut X) (g : G) :
    fixedLocus ρ g ≅ pullback (graph ρ g) (diagonal X) :=
  pullbackSymmetry (diagonal X) (graph ρ g)

/-- The residual automorphism of `X^g` induced by `h`, using that a commutative action preserves
the fixed locus of `g`. -/
def residualHom {S : Scheme.{u}} {G : Type u} [CommGroup G] {X : Over S}
    (ρ : G →* Aut X) (g h : G) : Aut (fixedLocus ρ g) where
  hom :=
    pullback.lift (inclusion ρ g ≫ (ρ h).hom) (inclusion ρ g ≫ (ρ h).hom) sorry
  inv :=
    pullback.lift (inclusion ρ g ≫ (ρ h⁻¹).hom) (inclusion ρ g ≫ (ρ h⁻¹).hom) sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The residual action of a commutative group on `X^g`. -/
def residual {S : Scheme.{u}} {G : Type u} [CommGroup G] {X : Over S}
    (ρ : G →* Aut X) (g : G) : G →* Aut (fixedLocus ρ g) where
  toFun := residualHom ρ g
  map_one' := sorry
  map_mul' := sorry

/-- The residual automorphism of `h` acts on the inclusion by `ρ h`. -/
theorem residual_hom {S : Scheme.{u}} {G : Type u} [CommGroup G] {X : Over S}
    (ρ : G →* Aut X) (g h : G) :
    (residual ρ g h).hom ≫ inclusion ρ g = inclusion ρ g ≫ (ρ h).hom :=
  sorry

/-- The residual action sends `1` to the identity automorphism of `X^g`. -/
theorem residual_one {S : Scheme.{u}} {G : Type u} [CommGroup G] {X : Over S}
    (ρ : G →* Aut X) (g : G) :
    residual ρ g 1 = 1 :=
  sorry

/-- The residual action preserves multiplication. -/
theorem residual_mul {S : Scheme.{u}} {G : Type u} [CommGroup G] {X : Over S}
    (ρ : G →* Aut X) (g h₁ h₂ : G) :
    residual ρ g (h₁ * h₂) = residual ρ g h₁ * residual ρ g h₂ :=
  sorry

/-- Scheme automorphisms as algebraic-space automorphisms, via Yoneda. -/
def ofOverAut {S : Scheme.{u}} {U : Over S} : Aut U →* Aut (ofOver U) where
  toFun α :=
    { hom := ofOverMap α.hom
      inv := ofOverMap α.inv
      hom_inv_id := sorry
      inv_hom_id := sorry }
  map_one' := sorry
  map_mul' := sorry

/-- The underlying morphism of `ofOverAut α` is the Yoneda image of `α`. -/
theorem ofOverAut_hom {S : Scheme.{u}} {U : Over S} (α : Aut U) :
    (ofOverAut α).hom = ofOverMap α.hom :=
  sorry

/-- The sheaf morphism on functors of points induced by a map of schemes over `S`. -/
def ofOverSheafMap {S : Scheme.{u}} {U V : Over S} (f : U ⟶ V) :
    toSheaf (ofOver U) ⟶ toSheaf (ofOver V) :=
  Sheaf.homEquiv.symm (ofOverMap f)

/-- The underlying presheaf map of `ofOverSheafMap f` is `ofOverMap f`. -/
theorem ofOverSheafMap_hom {S : Scheme.{u}} {U V : Over S} (f : U ⟶ V) :
    (ofOverSheafMap f).hom = ofOverMap f :=
  sorry

/-- The action morphism `∐_G X ⟶ X` sending the `g`-summand by `ρ g`. -/
def action {S : Scheme.{u}} {G : Type u} [Group G] {X : Over S}
    (ρ : G →* Aut X) : (∐ fun _ : G ↦ X) ⟶ X :=
  Sigma.desc fun g ↦ (ρ g).hom

/-- On the `g`-summand, `action ρ` is the automorphism `ρ g`. -/
theorem action_ι {S : Scheme.{u}} {G : Type u} [Group G] {X : Over S}
    (ρ : G →* Aut X) (g : G) :
    Sigma.ι (fun _ : G ↦ X) g ≫ action ρ = (ρ g).hom :=
  sorry

end AlgebraicGeometry.QuotientStack.FixedLocus
