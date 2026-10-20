module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale

/-!
# Open immersions and finite étale morphisms

The generating morphism property and descending finite-tower composition for schemes.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The generating class of open immersions and finite étale morphisms of schemes. -/
abbrev openImmersionOrFiniteEtale : MorphismProperty Scheme.{u} :=
  @IsOpenImmersion ⊔ Scheme.finiteEtaleMorphism

/-- A scheme morphism belongs to the generating class exactly when it is an open immersion
or a finite étale morphism. -/
theorem openImmersionOrFiniteEtale_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    openImmersionOrFiniteEtale f ↔ IsOpenImmersion f ∨ IsFinite f ∧ Etale f := sorry

namespace Scheme.Hom

/-- The composite of a descending finite tower runs from its last scheme to its first;
the zero-length tower has identity composite. -/
def towerComposite {n : ℕ} {W : Fin (n + 1) → Scheme.{u}}
    (step : ∀ index : Fin n, W index.succ ⟶ W index.castSucc) :
    W (Fin.last n) ⟶ W 0 :=
  Fin.induction (motive := fun index ↦ (W index ⟶ W 0)) (𝟙 (W 0))
    (fun index composite ↦ step index ≫ composite) (Fin.last n)

/-- The zero-length tower has composite the identity on its sole scheme. -/
theorem towerComposite_zero {W : Fin 1 → Scheme.{u}}
    (step : ∀ index : Fin 0, W index.succ ⟶ W index.castSucc) :
    towerComposite step = 𝟙 (W 0) := sorry

end Scheme.Hom

end AlgebraicGeometry
