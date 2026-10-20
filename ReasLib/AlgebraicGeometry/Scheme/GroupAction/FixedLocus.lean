module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Over

/-!
# Scheme-theoretic fixed loci of group actions

Fixed loci are diagonal–graph pullbacks. A commutative action restricts to an action on each
fixed locus.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.GroupAction.FixedLocus

/-- The graph of an action automorphism, with the identity as its second component. -/
def graph {S : Scheme.{u}} {G : Type u} [Group G] {X : Over S}
    (ρ : G →* Aut X) (g : G) : X ⟶ X ⨯ X :=
  prod.lift (ρ g).hom (𝟙 X)

/-- The scheme-theoretic fixed locus is the pullback of the diagonal and the action graph. -/
def fixedLocus {S : Scheme.{u}} {G : Type u} [Group G] {X : Over S}
    (ρ : G →* Aut X) (g : G) : Over S :=
  pullback (diag X) (graph ρ g)

/-- The first projection from the fixed locus to the scheme on which the group acts. -/
def inclusion {S : Scheme.{u}} {G : Type u} [Group G] {X : Over S}
    (ρ : G →* Aut X) (g : G) : fixedLocus ρ g ⟶ X :=
  pullback.fst (diag X) (graph ρ g)

/-- The two projections of the diagonal–graph pullback to the acting scheme coincide. -/
theorem fixedLocus_fst_eq_snd {S : Scheme.{u}} {G : Type u} [Group G] {X : Over S}
    (ρ : G →* Aut X) (g : G) :
    pullback.fst (diag X) (graph ρ g) = pullback.snd (diag X) (graph ρ g) :=
  sorry

/-- The fixed-locus projection equalizes the chosen action automorphism and the identity. -/
theorem inclusion_spec {S : Scheme.{u}} {G : Type u} [Group G] {X : Over S}
    (ρ : G →* Aut X) (g : G) :
    inclusion ρ g ≫ (ρ g).hom = inclusion ρ g :=
  sorry

/-- The fixed-locus projection has equal composites with the diagonal and the action graph. -/
theorem fixedLocus_condition {S : Scheme.{u}} {G : Type u} [Group G] {X : Over S}
    (ρ : G →* Aut X) (g : G) :
    inclusion ρ g ≫ diag X = inclusion ρ g ≫ graph ρ g :=
  sorry

/-- A commuting action automorphism carries the fixed-locus projection into the same pullback. -/
private theorem residualMap_condition {S : Scheme.{u}} {G : Type u} [CommGroup G]
    {X : Over S} (ρ : G →* Aut X) (g h : G) :
    (inclusion ρ g ≫ (ρ h).hom) ≫ diag X =
      (inclusion ρ g ≫ (ρ h).hom) ≫ graph ρ g :=
  sorry

/-- The restriction of an action automorphism to a fixed locus for a commuting element. -/
def residualMap {S : Scheme.{u}} {G : Type u} [CommGroup G] {X : Over S}
    (ρ : G →* Aut X) (g h : G) : fixedLocus ρ g ⟶ fixedLocus ρ g :=
  pullback.lift (inclusion ρ g ≫ (ρ h).hom) (inclusion ρ g ≫ (ρ h).hom)
    (by exact residualMap_condition ρ g h)

/-- Restricting the identity group element gives the identity on the fixed locus. -/
private theorem residualMap_one {S : Scheme.{u}} {G : Type u} [CommGroup G]
    {X : Over S} (ρ : G →* Aut X) (g : G) :
    residualMap ρ g 1 = 𝟙 (fixedLocus ρ g) :=
  sorry

/-- Restricted action maps respect multiplication in the order of automorphism multiplication. -/
private theorem residualMap_mul {S : Scheme.{u}} {G : Type u} [CommGroup G]
    {X : Over S} (ρ : G →* Aut X) (g h k : G) :
    residualMap ρ g (h * k) = residualMap ρ g k ≫ residualMap ρ g h :=
  sorry

/-- An action automorphism and its inverse restrict to an automorphism of each fixed locus. -/
def residualHom {S : Scheme.{u}} {G : Type u} [CommGroup G] {X : Over S}
    (ρ : G →* Aut X) (g h : G) : Aut (fixedLocus ρ g) where
  hom := residualMap ρ g h
  inv := residualMap ρ g h⁻¹
  hom_inv_id := by rw [← residualMap_mul, inv_mul_cancel, residualMap_one]
  inv_hom_id := by rw [← residualMap_mul, mul_inv_cancel, residualMap_one]

/-- The residual action of a commutative group on the fixed locus of one of its elements. -/
def residual {S : Scheme.{u}} {G : Type u} [CommGroup G] {X : Over S}
    (ρ : G →* Aut X) (g : G) : G →* Aut (fixedLocus ρ g) where
  toFun := residualHom ρ g
  map_one' := by
    apply Iso.ext
    exact residualMap_one ρ g
  map_mul' h k := by
    apply Iso.ext
    exact residualMap_mul ρ g h k

/-- The fixed-locus projection intertwines the residual action with the original action. -/
theorem residual_hom {S : Scheme.{u}} {G : Type u} [CommGroup G] {X : Over S}
    (ρ : G →* Aut X) (g h : G) :
    (residual ρ g h).hom ≫ inclusion ρ g = inclusion ρ g ≫ (ρ h).hom :=
  sorry

/-- The residual action sends the identity element to the identity automorphism. -/
theorem residual_one {S : Scheme.{u}} {G : Type u} [CommGroup G] {X : Over S}
    (ρ : G →* Aut X) (g : G) : residual ρ g 1 = 1 :=
  (residual ρ g).map_one

/-- The residual action preserves multiplication. -/
theorem residual_mul {S : Scheme.{u}} {G : Type u} [CommGroup G] {X : Over S}
    (ρ : G →* Aut X) (g h k : G) :
    residual ρ g (h * k) = residual ρ g h * residual ρ g k :=
  (residual ρ g).map_mul h k

/-- The action morphism from the coproduct of copies of the acting scheme. -/
def action {S : Scheme.{u}} {G : Type u} [Group G] {X : Over S}
    (ρ : G →* Aut X) : (∐ fun _ : G ↦ X) ⟶ X :=
  Limits.Sigma.desc fun g ↦ (ρ g).hom

/-- The action morphism on a summand is the automorphism indexed by that summand. -/
theorem action_ι {S : Scheme.{u}} {G : Type u} [Group G] {X : Over S}
    (ρ : G →* Aut X) (g : G) :
    Limits.Sigma.ι (fun _ : G ↦ X) g ≫ action ρ = (ρ g).hom :=
  sorry

end AlgebraicGeometry.Scheme.GroupAction.FixedLocus
