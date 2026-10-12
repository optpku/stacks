/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Standard simplices in a truncated simplex category

When `k ≤ n`, restricting the standard simplex `Δ[k]` to degrees at most `n` gives the
representable presheaf of the bundled truncated simplex `⦋k, hk⦌ₙ`. This file exposes that
identification and its Yoneda equivalence.
-/

@[expose] public section

open CategoryTheory Opposite
open SimplexCategory Truncated
open SSet.stdSimplex
open scoped Simplicial SimplexCategory.Truncated

universe u

namespace SSet.Truncated

/-- The morphism from the top truncated simplex determined by a simplex of a restricted standard
simplex. -/
@[stacks 017F "truncated standard simplex classification map"]
def stdSimplex.simplexMap {n k : ℕ} (hk : k ≤ n)
    (Δ : (SimplexCategory.Truncated n)ᵒᵖ)
    (u : ((SSet.truncation n).obj (Δ[k] : SSet.{u})).obj Δ) :
    op ⦋k,hk⦌ₙ ⟶ Δ :=
  (SimplexCategory.Truncated.Hom.tr (SSet.stdSimplex.objEquiv u) (unop Δ).property hk).op

namespace stdSimplex.simplexMap

/-- The morphisms determined by simplices of a restricted standard simplex commute with
truncated simplex operators. -/
@[stacks 017F "truncated standard simplex classification naturality"]
theorem naturality {n k : ℕ} (hk : k ≤ n)
    {Δ Δ' : (SimplexCategory.Truncated n)ᵒᵖ} (a : Δ ⟶ Δ')
    (u : ((SSet.truncation n).obj (Δ[k] : SSet.{u})).obj Δ) :
    stdSimplex.simplexMap hk Δ u ≫ a =
      stdSimplex.simplexMap hk Δ'
        (((SSet.truncation n).obj (Δ[k] : SSet.{u})).map a u) := sorry

/-- Acting on the identity `k`-simplex by the morphism determined by `u` recovers `u`. -/
@[stacks 017F "truncated standard simplex classification identity action"]
theorem map_identity {n k : ℕ} (hk : k ≤ n)
    (Δ : (SimplexCategory.Truncated n)ᵒᵖ)
    (u : ((SSet.truncation n).obj (Δ[k] : SSet.{u})).obj Δ) :
    ((SSet.truncation n).obj (Δ[k] : SSet.{u})).map
        (stdSimplex.simplexMap hk Δ u)
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋k⦌)) = u := sorry

/-- The morphism determined by the identity `k`-simplex is the identity morphism. -/
@[stacks 017F "truncated standard simplex classification identity map"]
theorem identity {n k : ℕ} (hk : k ≤ n) :
    stdSimplex.simplexMap hk (op ⦋k,hk⦌ₙ)
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋k⦌)) =
      𝟙 (op ⦋k,hk⦌ₙ) := sorry

end stdSimplex.simplexMap

/-- Send a simplex of the restricted standard simplex to its truncated representable map. -/
@[stacks 017F "truncated standard simplex object-equivalence map"]
def stdSimplex.objEquiv.forward {n k : ℕ} (hk : k ≤ n)
    {Δ : SimplexCategory.Truncated n}
    (x : ((SSet.truncation n).obj (Δ[k] : SSet.{u})).obj (op Δ)) :
    (uliftYoneda.{u}.obj ⦋k,hk⦌ₙ).obj (op Δ) :=
  ⟨ObjectProperty.homMk (SSet.stdSimplex.objEquiv x)⟩

/-- Recover a restricted standard-simplex simplex from its truncated representable map. -/
@[stacks 017F "truncated standard simplex object-equivalence inverse"]
def stdSimplex.objEquiv.inverse {n k : ℕ} (hk : k ≤ n)
    {Δ : SimplexCategory.Truncated n}
    (f : (uliftYoneda.{u}.obj ⦋k,hk⦌ₙ).obj (op Δ)) :
    ((SSet.truncation n).obj (Δ[k] : SSet.{u})).obj (op Δ) :=
  SSet.stdSimplex.objEquiv.symm f.down.hom

/-- Recovering a restricted simplex after passing to its representable map is the identity. -/
@[stacks 017F "truncated standard simplex object-equivalence left inverse"]
theorem stdSimplex.objEquiv.left_inv {n k : ℕ} (hk : k ≤ n)
    {Δ : SimplexCategory.Truncated n}
    (x : ((SSet.truncation n).obj (Δ[k] : SSet.{u})).obj (op Δ)) :
    stdSimplex.objEquiv.inverse hk (stdSimplex.objEquiv.forward hk x) = x := sorry

/-- Passing back to a representable map after recovering its simplex is the identity. -/
@[stacks 017F "truncated standard simplex object-equivalence right inverse"]
theorem stdSimplex.objEquiv.right_inv {n k : ℕ} (hk : k ≤ n)
    {Δ : SimplexCategory.Truncated n}
    (f : (uliftYoneda.{u}.obj ⦋k,hk⦌ₙ).obj (op Δ)) :
    stdSimplex.objEquiv.forward hk (stdSimplex.objEquiv.inverse hk f) = f := sorry

/-- Degreewise identification of a restricted standard simplex with the corresponding
representable presheaf on the truncated simplex category. -/
@[stacks 017F "truncated standard simplex object equivalence"]
def stdSimplex.objEquiv {n k : ℕ} (hk : k ≤ n) (Δ : SimplexCategory.Truncated n) :
    ((SSet.truncation n).obj (Δ[k] : SSet.{u})).obj (op Δ) ≃
      (uliftYoneda.{u}.obj ⦋k,hk⦌ₙ).obj (op Δ) where
  toFun := stdSimplex.objEquiv.forward hk
  invFun := stdSimplex.objEquiv.inverse hk
  left_inv := stdSimplex.objEquiv.left_inv hk
  right_inv := stdSimplex.objEquiv.right_inv hk

/-- The degreewise truncated standard-simplex equivalences are natural in the truncated
simplex. -/
@[stacks 017F "truncated standard simplex object-equivalence naturality"]
theorem stdSimplex.objEquiv.naturality {n k : ℕ} (hk : k ≤ n)
    {Δ Δ' : (SimplexCategory.Truncated n)ᵒᵖ} (a : Δ ⟶ Δ') :
    ((SSet.truncation n).obj (Δ[k] : SSet.{u})).map a ≫
        (stdSimplex.objEquiv hk (unop Δ')).toIso.hom =
      (stdSimplex.objEquiv hk (unop Δ)).toIso.hom ≫
        (uliftYoneda.{u}.obj ⦋k,hk⦌ₙ).map a := sorry

/-- Restriction of `Δ[k]` to degrees at most `n` is the representable presheaf of the truncated
simplex `⦋k, hk⦌ₙ`. -/
@[stacks 017F "truncated standard simplex representability"]
noncomputable def stdSimplex.iso {n k : ℕ} (hk : k ≤ n) :
    (SSet.truncation n).obj (Δ[k] : SSet.{u}) ≅ uliftYoneda.{u}.obj ⦋k,hk⦌ₙ :=
  NatIso.ofComponents (fun Δ ↦ (stdSimplex.objEquiv hk (unop Δ)).toIso)
    (stdSimplex.objEquiv.naturality hk)

namespace stdSimplex.iso

/-- The forward component of truncated standard-simplex representability is the explicit
degreewise object equivalence. -/
@[simp, stacks 017F "truncated standard simplex equivalence forward component"]
theorem hom_app {n k : ℕ} (hk : k ≤ n)
    (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    (stdSimplex.iso hk).hom.app Δ =
      (stdSimplex.objEquiv hk (unop Δ)).toIso.hom := sorry

/-- The inverse component of truncated standard-simplex representability is the inverse explicit
degreewise object equivalence. -/
@[simp, stacks 017F "truncated standard simplex equivalence inverse component"]
theorem inv_app {n k : ℕ} (hk : k ≤ n)
    (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    (stdSimplex.iso hk).inv.app Δ =
      (stdSimplex.objEquiv hk (unop Δ)).toIso.inv := sorry

end stdSimplex.iso

/-- Yoneda evaluation for a standard simplex restricted to a truncated simplex category. -/
@[stacks 017F "truncated standard simplex Yoneda equivalence"]
noncomputable def stdSimplex.homEquiv {n k : ℕ} (hk : k ≤ n)
    (U : SSet.Truncated.{u} n) :
    ((SSet.truncation n).obj (Δ[k] : SSet.{u}) ⟶ U) ≃ U.obj (op ⦋k,hk⦌ₙ) :=
  ((stdSimplex.iso hk).homCongr (Iso.refl U)).trans uliftYonedaEquiv

/-- The truncated standard-simplex Yoneda equivalence evaluates at the identity simplex. -/
@[stacks 017F "truncated standard simplex Yoneda evaluation"]
theorem stdSimplex.homEquiv.apply {n k : ℕ} (hk : k ≤ n)
    (U : SSet.Truncated.{u} n)
    (f : (SSet.truncation n).obj (Δ[k] : SSet.{u}) ⟶ U) :
    stdSimplex.homEquiv hk U f =
      f.app (op ⦋k,hk⦌ₙ) (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋k⦌)) := sorry

/-- Truncated standard-simplex Yoneda evaluation is natural under postcomposition. -/
@[stacks 017F "truncated standard simplex Yoneda naturality"]
theorem stdSimplex.homEquiv.naturality {n k : ℕ} (hk : k ≤ n)
    {U V : SSet.Truncated.{u} n}
    (f : (SSet.truncation n).obj (Δ[k] : SSet.{u}) ⟶ U) (g : U ⟶ V) :
    stdSimplex.homEquiv hk V (f ≫ g) =
      g.app (op ⦋k,hk⦌ₙ) (stdSimplex.homEquiv hk U f) := sorry

end SSet.Truncated
