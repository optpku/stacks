/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.EilenbergMacLane.Extension.Index
public import Mathlib.AlgebraicTopology.DoldKan.FunctorGamma
public import ReasLib.CategoryTheory.Limits.Shapes.Coproducts.Diagonal

/-!
@stack 0192

# Degreewise coproduct decomposition of Eilenberg-MacLane extensions

This file identifies every simplicial degree of the extension object with the coproduct of its
two adjacent families of coefficient summands. It owns the objectwise and natural isomorphisms,
the summand inclusions, and their behavior under simplicial structure maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomologicalComplex
open scoped Simplicial DoldKan

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.eilenbergMacLane.extension.sum

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [HasZeroObject 𝒜]
variable [HasFiniteCoproducts 𝒜]

namespace simplex

/-- For fixed `k` and `n`, evaluate the Eilenberg-MacLane extension functor in simplicial
degree `n`. -/
@[stacks 0192 "degreewise Eilenberg-MacLane extension coefficient functor"]
noncomputable abbrev functor (k n : ℕ) : 𝒜 ⥤ 𝒜 :=
  extension.functor (𝒜 := 𝒜) k ⋙
    (evaluation SimplexCategoryᵒᵖ 𝒜).obj (Opposite.op ⦋n⦌)

/-- Evaluating the degreewise extension functor gives the degree-`n` extension object. -/
@[simp, stacks 0192 "degreewise Eilenberg-MacLane extension object formula"]
theorem functor_obj (k n : ℕ) (A : 𝒜) :
    (functor (𝒜 := 𝒜) k n).obj A =
      (object A k).obj (Opposite.op ⦋n⦌) := sorry

/-- The degreewise extension functor evaluates the coefficient map in simplicial degree
`n`. -/
@[simp, stacks 0192 "degreewise Eilenberg-MacLane extension map formula"]
theorem functor_map (k n : ℕ) {A B : 𝒜} (f : A ⟶ B) :
    (functor (𝒜 := 𝒜) k n).map f =
      ((extension.functor (𝒜 := 𝒜) k).map f).app (Opposite.op ⦋n⦌) := sorry

end simplex

/-- The chain-complex summand selected by an extension index is canonically isomorphic to the
coefficient object. -/
@[stacks 0192 "Eilenberg-MacLane extension coefficient summand"]
noncomputable def termIso (A : 𝒜) {k n : ℕ} (a : Index k n) :
    (ChainComplex.disk A k).X a.toSplitIndex.1.unop.len ≅ A :=
  match a with
  | .inl _ => ChainComplex.disk.lowerIso A k
  | .inr _ => ChainComplex.disk.upperIso A k

/-- The inclusion of the summand selected by `a` into the extension object. -/
@[stacks 0192 "Eilenberg-MacLane extension summand inclusion"]
noncomputable def inclusion (A : 𝒜) {k n : ℕ} (a : Index k n) :
    A ⟶ (object A k).obj (Opposite.op ⦋n⦌) :=
  (termIso A a).inv ≫
    ((AlgebraicTopology.DoldKan.Γ₀.splitting
      (ChainComplex.disk A k)).cofan (Opposite.op ⦋n⦌)).inj a.toSplitIndex

namespace simplex

/-- A coefficient morphism commutes with the inclusion of a fixed summand into the degreewise
Eilenberg-MacLane extension object. -/
@[stacks 0192 "extension summand coefficient naturality"]
theorem inclusion.naturality {k n : ℕ} (a : Index k n) {A B : 𝒜} (f : A ⟶ B) :
    f ≫ sum.inclusion B a =
      sum.inclusion A a ≫ (functor (𝒜 := 𝒜) k n).map f := sorry

/-- The inclusion of a fixed extension summand, natural in the coefficient object. -/
@[stacks 0192 "natural Eilenberg-MacLane extension summand inclusion"]
noncomputable def inclusion {k n : ℕ} (a : Index k n) :
    𝟭 𝒜 ⟶ functor (𝒜 := 𝒜) k n where
  app A := sum.inclusion A a
  naturality _ _ f := inclusion.naturality a f

/-- The component of the natural extension-summand inclusion is the explicit summand map. -/
@[simp, stacks 0192 "natural Eilenberg-MacLane extension summand inclusion component"]
theorem inclusion.app {k n : ℕ} (a : Index k n) (A : 𝒜) :
    (inclusion (𝒜 := 𝒜) a).app A = sum.inclusion A a := sorry

end simplex

/-- The map from the full Dold-Kan coproduct to the coproduct indexed only by the two nonzero
degrees of the extension complex. -/
@[stacks 0192 "Eilenberg-MacLane extension coproduct projection"]
noncomputable def toCoproduct (A : 𝒜) (k n : ℕ) :
    (object A k).obj (Opposite.op ⦋n⦌) ⟶
      ∐ fun _ : Index k n ↦ A :=
  (AlgebraicTopology.DoldKan.Γ₀.splitting (ChainComplex.disk A k)).desc
    (Opposite.op ⦋n⦌) fun α ↦
      if hk : α.1.unop.len = k then
        ((ChainComplex.disk A k).XIsoOfEq hk).hom ≫
          (ChainComplex.disk.lowerIso A k).hom ≫
          Limits.Sigma.ι (fun _ : Index k n ↦ A)
            (.inl ⟨α.e ≫ eqToHom (SimplexCategory.ext hk), inferInstance⟩)
      else if hk₁ : α.1.unop.len = k + 1 then
        ((ChainComplex.disk A k).XIsoOfEq hk₁).hom ≫
          (ChainComplex.disk.upperIso A k).hom ≫
          Limits.Sigma.ι (fun _ : Index k n ↦ A)
            (.inr ⟨α.e ≫ eqToHom (SimplexCategory.ext hk₁), inferInstance⟩)
      else
        0

/-- The map from the extension-indexed coproduct to the explicit Dold-Kan coproduct. -/
@[stacks 0192 "Eilenberg-MacLane extension coproduct lift"]
noncomputable def fromCoproduct (A : 𝒜) (k n : ℕ) :
    (∐ fun _ : Index k n ↦ A) ⟶
      (object A k).obj (Opposite.op ⦋n⦌) :=
  Limits.Sigma.desc fun a : Index k n ↦ inclusion A a

/-- The explicit projection followed by the summand lift is the identity. -/
@[stacks 0192 "Eilenberg-MacLane extension coproduct forward inverse law"]
theorem iso.hom_inv_id (A : 𝒜) (k n : ℕ) :
    toCoproduct A k n ≫ fromCoproduct A k n = 𝟙 _ := sorry

/-- The summand lift followed by the explicit projection is the identity. -/
@[stacks 0192 "Eilenberg-MacLane extension coproduct inverse forward law"]
theorem iso.inv_hom_id (A : 𝒜) (k n : ℕ) :
    fromCoproduct A k n ≫ toCoproduct A k n = 𝟙 _ := sorry

/-- The degree-`n` extension object is the coproduct of copies of `A` indexed by epimorphisms
to `[k]` and `[k + 1]`. -/
@[stacks 0192 "degreewise Eilenberg-MacLane extension coproduct decomposition"]
noncomputable def iso (A : 𝒜) (k n : ℕ) :
    (object A k).obj (Opposite.op ⦋n⦌) ≅
      ∐ fun _ : Index k n ↦ A where
  hom := toCoproduct A k n
  inv := fromCoproduct A k n
  hom_inv_id := iso.hom_inv_id A k n
  inv_hom_id := iso.inv_hom_id A k n

/-- The forward map of the degreewise extension decomposition is `toCoproduct`. -/
@[simp, stacks 0192 "Eilenberg-MacLane extension decomposition forward map"]
theorem iso.hom (A : 𝒜) (k n : ℕ) :
    (iso A k n).hom = toCoproduct A k n := sorry

/-- The inverse map of the degreewise extension decomposition is `fromCoproduct`. -/
@[simp, stacks 0192 "Eilenberg-MacLane extension decomposition inverse map"]
theorem iso.inv (A : 𝒜) (k n : ℕ) :
    (iso A k n).inv = fromCoproduct A k n := sorry

/-- Under the explicit coproduct decomposition, `ι A a` is the canonical inclusion of the
`a`-summand. -/
@[simp, stacks 0192 "Eilenberg-MacLane extension decomposition on summand inclusions"]
theorem iso.inclusion_hom (A : 𝒜) {k n : ℕ} (a : Index k n) :
    inclusion A a ≫ (iso A k n).hom =
      Limits.Sigma.ι (fun _ : Index k n ↦ A) a := sorry

/-- The inverse degreewise extension decomposition sends a coefficient-coproduct inclusion to
the corresponding extension-summand inclusion. -/
@[simp, stacks 0192 "inverse Eilenberg-MacLane extension decomposition on summands"]
theorem iso.inclusion_inv (A : 𝒜) {k n : ℕ} (a : Index k n) :
    Limits.Sigma.ι (fun _ : Index k n ↦ A) a ≫ (iso A k n).inv =
      inclusion A a := sorry

/-- The forward maps of the explicit coproduct decomposition are natural in the coefficient
object. -/
@[stacks 0192 "Eilenberg-MacLane extension coproduct forward naturality"]
theorem iso.hom_naturality (k n : ℕ) {A B : 𝒜} (f : A ⟶ B) :
    (simplex.functor (𝒜 := 𝒜) k n).map f ≫ (iso B k n).hom =
      (iso A k n).hom ≫
        (Limits.Sigma.diagonal (C := 𝒜) (Index k n)).map f := sorry

/-- The inverse maps of the explicit coproduct decomposition are natural in the coefficient
object. -/
@[stacks 0192 "Eilenberg-MacLane extension coproduct inverse naturality"]
theorem iso.inv_naturality (k n : ℕ) {A B : 𝒜} (f : A ⟶ B) :
    (Limits.Sigma.diagonal (C := 𝒜) (Index k n)).map f ≫ (iso B k n).inv =
      (iso A k n).inv ≫ (simplex.functor (𝒜 := 𝒜) k n).map f := sorry

/-- In fixed simplicial degree, the Eilenberg-MacLane extension functor is naturally
isomorphic to the coproduct of its coefficient summands. -/
@[stacks 0192 "natural degreewise Eilenberg-MacLane extension coproduct decomposition"]
noncomputable def natIso (k n : ℕ) :
    simplex.functor (𝒜 := 𝒜) k n ≅
      Limits.Sigma.diagonal (C := 𝒜) (Index k n) :=
  NatIso.ofComponents (fun A ↦ sum.iso A k n)
    (fun f ↦ sum.iso.hom_naturality k n f)

/-- The component of the natural coefficient decomposition is its objectwise coproduct
isomorphism. -/
@[simp, stacks 0192 "natural coefficient decomposition component"]
theorem natIso.app (k n : ℕ) (A : 𝒜) :
    (natIso (𝒜 := 𝒜) k n).app A = sum.iso A k n := sorry

/-- The forward component of the natural coefficient decomposition is the explicit objectwise
forward map. -/
@[simp, stacks 0192 "natural coefficient decomposition forward component"]
theorem natIso.hom_app (k n : ℕ) (A : 𝒜) :
    (natIso (𝒜 := 𝒜) k n).hom.app A = (sum.iso A k n).hom := sorry

/-- The inverse component of the natural coefficient decomposition is the explicit objectwise
inverse map. -/
@[simp, stacks 0192 "natural coefficient decomposition inverse component"]
theorem natIso.inv_app (k n : ℕ) (A : 𝒜) :
    (natIso (𝒜 := 𝒜) k n).inv.app A = (sum.iso A k n).inv := sorry

/-- The natural coefficient decomposition carries each extension-summand inclusion to the
corresponding coefficient-coproduct inclusion. -/
@[simp, stacks 0192 "natural coefficient decomposition on summand inclusions"]
theorem natIso.inclusion_hom {k n : ℕ} (a : Index k n) :
    simplex.inclusion (𝒜 := 𝒜) a ≫ (natIso (𝒜 := 𝒜) k n).hom =
      Limits.Sigma.diagonal.ι (C := 𝒜) a := sorry

/-- The inverse natural coefficient decomposition carries each coefficient-coproduct inclusion
back to the corresponding extension-summand inclusion. -/
@[simp, stacks 0192 "inverse natural coefficient decomposition on summand inclusions"]
theorem natIso.inclusion_inv {k n : ℕ} (a : Index k n) :
    Limits.Sigma.diagonal.ι (C := 𝒜) a ≫ (natIso (𝒜 := 𝒜) k n).inv =
      simplex.inclusion (𝒜 := 𝒜) a := sorry

/-- A simplicial structure map sends a summand along `Index.pull`; when the pull is undefined,
the summand is sent to zero. -/
@[stacks 0192 "Eilenberg-MacLane extension structure map on summands"]
theorem inclusion.map (A : 𝒜) {k m n : ℕ}
    (φ : ⦋m⦌ ⟶ ⦋n⦌) (a : Index k n) :
    inclusion A a ≫ (object A k).map φ.op =
      Option.elim (a.pull φ) 0 (fun b ↦ inclusion A b) := sorry

/-- If an extension index pulls back to `b`, the simplicial structure map carries its summand
inclusion to the inclusion of `b`. -/
@[simp, stacks 0192 "extension structure map after a successful summand pull"]
theorem inclusion.map_of_some (A : 𝒜) {k m n : ℕ}
    (φ : ⦋m⦌ ⟶ ⦋n⦌) (a : Index k n) {b : Index k m}
    (h : a.pull φ = some b) :
    inclusion A a ≫ (object A k).map φ.op = inclusion A b := sorry

/-- If an extension index has no pullback, the simplicial structure map kills its summand
inclusion. -/
@[simp, stacks 0192 "extension structure map after an absent summand pull"]
theorem inclusion.map_of_none (A : 𝒜) {k m n : ℕ}
    (φ : ⦋m⦌ ⟶ ⦋n⦌) (a : Index k n)
    (h : a.pull φ = none) :
    inclusion A a ≫ (object A k).map φ.op = 0 := sorry

end CategoryTheory.SimplicialObject.eilenbergMacLane.extension.sum
