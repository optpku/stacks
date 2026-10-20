module

public import ReasLib.AlgebraicTopology.SimplicialSet.Homotopy.Coskeletal
import StacksCheckRecall

/-!
@stack 01A9

# Lemma 14.32.2 compatibility facade

ReasLib owns both the directed simplicial-set homotopy produced by low-degree agreement with a
coskeletal target and its image in the reusable zigzag homotopy relation. The shared results do
not require the source to be coskeletal; this facade retains that source assumption while placing
the relation-valued textbook conclusion first.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.SimplicialObject
open scoped Simplicial

universe u

/- Lemma 14.32.2: if `f₀, f₁ : V ⟶ U` agree in degrees below `n`, and both `V` and `U`
are `n`-coskeletal, then `f₀` and `f₁` are homotopic. -/
@[stacks 01A9 "Lemma 14.32.2"]
#check (fun {V U : SSet.{u}} {n : ℕ} {f₀ f₁ : V ⟶ U}
    [U.IsCoskeletal n] (_ : V.IsCoskeletal n)
    (hbelow : ∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) ↦
      SimplicialObject.Homotopic.coskeletal.ofEqBelow hbelow :
  ∀ {V U : SSet.{u}} {n : ℕ} {f₀ f₁ : V ⟶ U} [U.IsCoskeletal n],
    V.IsCoskeletal n →
      (∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) →
        SimplicialObject.Homotopic f₀ f₁)

/- The canonical owner proves the stronger directed simplicial-set homotopy without assuming
that the source is coskeletal. -/
#check (@SSet.Homotopy.coskeletal.ofEqBelow.{u} :
  ∀ {V U : SSet.{u}} {n : ℕ} {f₀ f₁ : V ⟶ U} [U.IsCoskeletal n],
    (∀ i < n, f₀.app (op ⦋i⦌) = f₁.app (op ⦋i⦌)) →
      SSet.Homotopy f₀ f₁)
