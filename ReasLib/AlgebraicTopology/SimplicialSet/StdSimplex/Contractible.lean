module

public import ReasLib.AlgebraicTopology.SimplicialObject.HomotopyEquiv
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 08Q3

# Contractibility of standard simplices

The standard simplex `Δ[m]` contracts to its last vertex. The degreewise formula, simplicial map,
directed homotopy, and resulting homotopy equivalence with `Δ[0]` are exposed separately.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open SSet (const ι₀ ι₁)
open SSet.stdSimplex (asOrderHom isTerminalObj₀ obj₀Equiv objMk)
open scoped Simplicial

noncomputable section

namespace SSet.stdSimplex

/-- The last-vertex contraction formula is monotone in every simplicial degree. -/
@[stacks 08Q3 "last-vertex contraction monotonicity"]
theorem contractionApp.monotone (m : ℕ) (Δ : SimplexCategoryᵒᵖ)
    (z : (((Δ[m] : SSet) ⊗ Δ[1]).obj Δ)) :
    Monotone
      (fun k : Fin (Δ.unop.len + 1) ↦
        if asOrderHom z.2 k = 0 then asOrderHom z.1 k else Fin.last m) := sorry

/-- The degreewise function contracting `Δ[m] × Δ[1]` to the last vertex of `Δ[m]`. -/
@[stacks 08Q3 "degreewise last-vertex contraction"]
def contractionApp (m : ℕ) (Δ : SimplexCategoryᵒᵖ) :
    (((Δ[m] : SSet) ⊗ Δ[1]).obj Δ) → (Δ[m] : SSet).obj Δ :=
  fun z ↦
    objMk
      { toFun := fun k ↦
          if asOrderHom z.2 k = 0 then asOrderHom z.1 k else Fin.last m
        monotone' := contractionApp.monotone m Δ z }

/-- The degreewise last-vertex contraction formula commutes with simplicial operators. -/
@[stacks 08Q3 "degreewise last-vertex contraction computation"]
theorem contractionApp.naturality_apply (m : ℕ) {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ')
    (z : (((Δ[m] : SSet) ⊗ Δ[1]).obj Δ)) :
    contractionApp m Δ' (((Δ[m] : SSet) ⊗ Δ[1]).map θ z) =
      (Δ[m] : SSet).map θ (contractionApp m Δ z) := sorry

/-- Naturality of the degreewise contraction, in morphism form. -/
@[stacks 08Q3 "degreewise last-vertex contraction naturality"]
theorem contractionApp.naturality (m : ℕ) {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') :
    ((Δ[m] : SSet) ⊗ Δ[1]).map θ ≫
        ConcreteCategory.ofHom ⟨contractionApp m Δ'⟩ =
      ConcreteCategory.ofHom ⟨contractionApp m Δ⟩ ≫ (Δ[m] : SSet).map θ := sorry

/-- The simplicial map contracting `Δ[m] × Δ[1]` to the last vertex of `Δ[m]`. -/
@[stacks 08Q3 "last-vertex contraction"]
def contraction (m : ℕ) : (Δ[m] : SSet) ⊗ Δ[1] ⟶ Δ[m] where
  app Δ := ConcreteCategory.ofHom ⟨contractionApp m Δ⟩
  naturality := fun {_ _} θ ↦ contractionApp.naturality m θ

/-- The component of the bundled last-vertex contraction is `contractionApp`. -/
@[simp, stacks 08Q3 "last-vertex contraction component formula"]
theorem contraction.app (m : ℕ) (Δ : SimplexCategoryᵒᵖ) :
    (contraction m).app Δ = ConcreteCategory.ofHom ⟨contractionApp m Δ⟩ := sorry

namespace contraction

/-- At the zero endpoint, the last-vertex contraction is the identity. -/
@[stacks 08Q3 "last-vertex contraction zero endpoint"]
theorem endpointZero (m : ℕ) :
    ι₀ ≫ contraction m = 𝟙 (Δ[m] : SSet) := sorry

/-- At the one endpoint, the last-vertex contraction is the constant map at the last vertex. -/
@[stacks 08Q3 "last-vertex contraction one endpoint"]
theorem endpointOne (m : ℕ) :
    ι₁ ≫ contraction m =
      isTerminalObj₀.from (Δ[m] : SSet) ≫ SSet.const (obj₀Equiv.symm (Fin.last m)) := sorry

/-- The last-vertex contraction agrees on the empty relative subcomplex. -/
@[stacks 08Q3 "last-vertex contraction relative restriction"]
theorem rel (m : ℕ) :
    (⊥ : (Δ[m] : SSet).Subcomplex).ι ▷ (Δ[1] : SSet) ≫ contraction m =
      SemiCartesianMonoidalCategory.fst _ _ ≫ Subcomplex.isInitialBot.to _ ≫
        (⊥ : (Δ[m] : SSet).Subcomplex).ι := sorry

end contraction

/-- The directed homotopy from the identity of `Δ[m]` to the constant last-vertex map. -/
@[stacks 08Q3 "standard simplex contraction homotopy"]
def contraction.homotopy (m : ℕ) :
    SSet.Homotopy (𝟙 (Δ[m] : SSet))
      (isTerminalObj₀.from (Δ[m] : SSet) ≫ SSet.const (obj₀Equiv.symm (Fin.last m))) where
  h := contraction m
  h₀ := contraction.endpointZero m
  h₁ := contraction.endpointOne m
  rel := contraction.rel m

namespace homotopy

/-- The terminal and last-vertex maps satisfy the first homotopy-inverse law. -/
@[stacks 08Q3 "standard simplex contraction homotopy inverse law"]
theorem hom_inv_id (m : ℕ) :
    SimplicialObject.Homotopic
      (isTerminalObj₀.from (Δ[m] : SSet) ≫ SSet.const (obj₀Equiv.symm (Fin.last m)))
      (𝟙 (Δ[m] : SSet)) := sorry

/-- The terminal and last-vertex maps satisfy the second homotopy-inverse law. -/
@[stacks 08Q3 "standard simplex contraction inverse homotopy law"]
theorem inv_hom_id (m : ℕ) :
    SimplicialObject.Homotopic
      (SSet.const (obj₀Equiv.symm (Fin.last m)) ≫ isTerminalObj₀.from (Δ[m] : SSet))
      (𝟙 (Δ[0] : SSet)) := sorry

end homotopy

/-- Example 14.26.7 (08Q3): the standard simplex `Δ[m]` is homotopy equivalent to `Δ[0]`. -/
@[stacks 08Q3 "standard simplex is contractible"]
def homotopyEquiv (m : ℕ) :
    SimplicialObject.HomotopyEquiv (Δ[m] : SSet) (Δ[0] : SSet) where
  hom := isTerminalObj₀.from (Δ[m] : SSet)
  inv := SSet.const (obj₀Equiv.symm (Fin.last m))
  hom_inv_id := homotopy.hom_inv_id m
  inv_hom_id := homotopy.inv_hom_id m

/-- The forward map of the standard-simplex contraction equivalence is the terminal map. -/
@[simp, stacks 08Q3 "forward map of the standard simplex contraction equivalence"]
theorem homotopyEquiv.hom (m : ℕ) :
    (homotopyEquiv m).hom = isTerminalObj₀.from (Δ[m] : SSet) := sorry

/-- The inverse map of the standard-simplex contraction equivalence is the constant last-vertex
map. -/
@[simp, stacks 08Q3 "inverse map of the standard simplex contraction equivalence"]
theorem homotopyEquiv.inv (m : ℕ) :
    (homotopyEquiv m).inv = SSet.const (obj₀Equiv.symm (Fin.last m)) := sorry

end SSet.stdSimplex
