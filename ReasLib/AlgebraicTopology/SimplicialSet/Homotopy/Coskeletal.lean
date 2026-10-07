module

public import ReasLib.AlgebraicTopology.SimplicialObject.Homotopy
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Coskeleton.Coskeletal
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 01A9

# Homotopies into coskeletal simplicial sets

Two maps into an `n`-coskeletal simplicial set admit a canonical directed homotopy as soon as
their components agree in every degree strictly below `n`. The construction first defines the
cylinder map through degree `n`, then extends it across the coskeleton adjunction.

The source need not be coskeletal. This is the natural reusable strengthening of the usual
statement in which both source and target are assumed to be `n`-coskeletal.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.SimplicialObject
open scoped MonoidalCategory Simplicial

noncomputable section

universe u

namespace SSet.Homotopy

variable {V U : SSet.{u}} {n : ℕ} {f₀ f₁ : V ⟶ U}

namespace cylinder

namespace truncated

/-- The degreewise map on the truncated cylinder. In degree `n`, it uses `f₁` precisely on
the constant-one side of `Δ[1]`; in lower degrees it uses `f₀`. -/
@[stacks 01A9 "truncated coskeletal-cylinder component"]
def app {n : ℕ} (f₀ f₁ : V ⟶ U)
    (Θ : (SimplexCategory.Truncated n)ᵒᵖ) :
    (((SSet.truncation n).obj (V ⊗ Δ[1])).obj Θ) ⟶
      (((SSet.truncation n).obj U).obj Θ) :=
  ↾fun x ↦
    if Θ.unop.1.len = n then
      if SSet.stdSimplex.asOrderHom x.2 0 = (1 : Fin 2) then
        f₁.app (op Θ.unop.1) x.1
      else
        f₀.app (op Θ.unop.1) x.1
    else
      f₀.app (op Θ.unop.1) x.1

/-- Agreement of `f₀` and `f₁` below `n` makes `cylinder.truncated.app` natural on the
`n`-truncated simplex category. -/
@[stacks 01A9 "truncated coskeletal-cylinder naturality"]
theorem app_naturality
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌))
    {Θ₁ Θ₂ : (SimplexCategory.Truncated n)ᵒᵖ} (φ : Θ₁ ⟶ Θ₂) :
    ((SSet.truncation n).obj (V ⊗ Δ[1])).map φ ≫
        app f₀ f₁ Θ₂ =
      app f₀ f₁ Θ₁ ≫
        ((SSet.truncation n).obj U).map φ := sorry

/-- The morphism of `n`-truncated simplicial sets determined by `cylinder.truncated.app`. -/
@[stacks 01A9 "truncated coskeletal-cylinder morphism"]
def hom
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) :
    (SSet.truncation n).obj (V ⊗ Δ[1]) ⟶ (SSet.truncation n).obj U where
  app Θ := app f₀ f₁ Θ
  naturality := fun {_ _} φ ↦ app_naturality hbelow φ

/-- The component of the bundled truncated cylinder map is `cylinder.truncated.app`. -/
@[simp, stacks 01A9 "truncated coskeletal-cylinder component formula"]
theorem hom_app
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌))
    (Θ : (SimplexCategory.Truncated n)ᵒᵖ) :
    (hom hbelow).app Θ = app f₀ f₁ Θ := sorry

/-- The truncated cylinder restricts to `f₀` at the zero endpoint. -/
@[stacks 01A9 "truncated coskeletal-cylinder zero endpoint"]
theorem hom.zero
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) :
    (SSet.truncation n).map (ι₀ : V ⟶ V ⊗ Δ[1]) ≫ hom hbelow =
      (SSet.truncation n).map f₀ := sorry

/-- The truncated cylinder restricts to `f₁` at the one endpoint. -/
@[stacks 01A9 "truncated coskeletal-cylinder one endpoint"]
theorem hom.one
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) :
    (SSet.truncation n).map (ι₁ : V ⟶ V ⊗ Δ[1]) ≫ hom hbelow =
      (SSet.truncation n).map f₁ := sorry

end truncated

namespace coskeletal

/-- The cylinder map obtained by extending `cylinder.truncated.hom` into an `n`-coskeletal
target. -/
@[stacks 01A9 "coskeletal-cylinder morphism"]
noncomputable def hom [U.IsCoskeletal n]
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) :
    V ⊗ Δ[1] ⟶ U :=
  ((coskAdj n).homEquiv (V ⊗ Δ[1]) ((SSet.truncation n).obj U))
      (truncated.hom hbelow) ≫
    (U.isoCoskOfIsCoskeletal n).inv

/-- Extending the truncated cylinder map into a coskeletal target and then truncating recovers
the original truncated cylinder map. -/
@[stacks 01A9 "coskeletal-cylinder truncation formula"]
theorem truncation_hom [U.IsCoskeletal n]
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) :
    (SSet.truncation n).map (hom hbelow) = truncated.hom hbelow := sorry

/-- The coskeletal cylinder restricts to `f₀` at the zero endpoint. -/
@[stacks 01A9 "coskeletal-cylinder zero endpoint"]
theorem hom.zero [U.IsCoskeletal n]
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) :
    (ι₀ : V ⟶ V ⊗ Δ[1]) ≫ hom hbelow = f₀ := sorry

/-- The coskeletal cylinder restricts to `f₁` at the one endpoint. -/
@[stacks 01A9 "coskeletal-cylinder one endpoint"]
theorem hom.one [U.IsCoskeletal n]
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) :
    (ι₁ : V ⟶ V ⊗ Δ[1]) ≫ hom hbelow = f₁ := sorry

/-- The relative condition for `cylinder.coskeletal.hom` on the bottom subcomplex is vacuous. -/
@[stacks 01A9 "coskeletal-cylinder bottom-relative condition"]
theorem hom.bot [U.IsCoskeletal n]
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) :
    (⊥ : V.Subcomplex).ι ▷ Δ[1] ≫ hom hbelow =
      fst (⊥ : V.Subcomplex).toSSet Δ[1] ≫
        SSet.Subcomplex.isInitialBot.to (⊥ : U.Subcomplex).toSSet ≫
          (⊥ : U.Subcomplex).ι := sorry

end coskeletal

end cylinder

namespace coskeletal

/-- Lemma 14.32.2 (01A9), in its reusable directed form: maps into an `n`-coskeletal
simplicial set which agree in degrees below `n` admit a simplicial-set homotopy. -/
@[stacks 01A9 "low-degree agreement gives a homotopy into a coskeletal simplicial set"]
noncomputable def ofEqBelow [U.IsCoskeletal n]
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) :
    SSet.Homotopy f₀ f₁ where
  h := cylinder.coskeletal.hom hbelow
  h₀ := cylinder.coskeletal.hom.zero hbelow
  h₁ := cylinder.coskeletal.hom.one hbelow
  rel := cylinder.coskeletal.hom.bot hbelow

end coskeletal

end SSet.Homotopy

namespace CategoryTheory.SimplicialObject.Homotopic

variable {V U : SSet.{u}} {n : ℕ} {f₀ f₁ : V ⟶ U}

namespace coskeletal

/-- Low-degree agreement into an `n`-coskeletal simplicial set implies the zigzag relation
generated by combinatorial simplicial-object homotopies. -/
@[stacks 01A9 "coskeletal simplicial-set homotopies induce the zigzag relation"]
theorem ofEqBelow [U.IsCoskeletal n]
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) :
    CategoryTheory.SimplicialObject.Homotopic f₀ f₁ := sorry

end coskeletal

end CategoryTheory.SimplicialObject.Homotopic
