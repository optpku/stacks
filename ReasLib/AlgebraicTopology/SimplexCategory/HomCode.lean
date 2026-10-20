module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Generator codes for simplex morphisms

This module owns a typed word in cofaces and codegeneracies for every morphism between skeletal
finite ordinals.  The recursive construction deterministically scans for the first omitted target
vertex or adjacent repeated source value, then uses explicit factor morphisms.  Downstream
consumers should use `ofHom.toHom` rather than inspect the resulting word.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

namespace SimplexCategory

universe v

namespace Hom

/-- The first target vertex omitted by a simplex morphism, when such a vertex exists. -/
@[stacks 0G5N "first omitted target vertex of a simplex morphism"]
def targetGap? {Delta : SimplexCategory} {n : ℕ}
    (f : Delta ⟶ SimplexCategory.mk n) :
    Option (Fin (n + 1)) :=
  (List.finRange (n + 1)).find? (fun i =>
    decide (∀ j : Fin (Delta.len + 1), f.toOrderHom j ≠ i))

/-- A target vertex returned by `targetGap?` is not in the image of the simplex morphism. -/
@[stacks 0G5N "omitted target vertex specification"]
theorem targetGap_spec {Delta : SimplexCategory} {n : ℕ}
    (f : Delta ⟶ SimplexCategory.mk n)
    {i : Fin (n + 1)} (hi : targetGap? f = some i) :
    ∀ j : Fin (Delta.len + 1), f.toOrderHom j ≠ i := sorry

/-- Every target vertex before the one returned by `targetGap?` lies in the image. -/
@[stacks 0G5N "minimality of the first omitted target vertex"]
theorem targetGap_minimal {Delta : SimplexCategory} {n : ℕ}
    (f : Delta ⟶ SimplexCategory.mk n)
    {i : Fin (n + 1)} (hi : targetGap? f = some i) :
    ∀ j : Fin (n + 1), j < i →
      ∃ k : Fin (Delta.len + 1), f.toOrderHom k = j := sorry

/-- The target-gap scan succeeds exactly for nonsurjective simplex morphisms. -/
@[simp, stacks 0G5N "omitted target vertex existence criterion"]
theorem targetGap_isSome_iff {Delta : SimplexCategory} {n : ℕ}
    (f : Delta ⟶ SimplexCategory.mk n) :
    (targetGap? f).isSome ↔ ¬Function.Surjective f.toOrderHom := sorry

/-- The first adjacent pair on which a simplex morphism has equal values, when one exists. -/
@[stacks 0G5N "first adjacent repetition of a simplex morphism"]
def domainRepeat? {m : ℕ} {Delta : SimplexCategory}
    (f : SimplexCategory.mk (m + 1) ⟶ Delta) :
    Option (Fin (m + 1)) :=
  (List.finRange (m + 1)).find? (fun i =>
    decide (f.toOrderHom i.castSucc = f.toOrderHom i.succ))

/-- An index returned by `domainRepeat?` is an adjacent repeated value of the morphism. -/
@[stacks 0G5N "adjacent repeated value specification"]
theorem domainRepeat_spec {m : ℕ} {Delta : SimplexCategory}
    (f : SimplexCategory.mk (m + 1) ⟶ Delta)
    {i : Fin (m + 1)} (hi : domainRepeat? f = some i) :
    f.toOrderHom i.castSucc = f.toOrderHom i.succ := sorry

/-- No domain index before the one returned by `domainRepeat?` has an adjacent repeated value. -/
@[stacks 0G5N "minimality of the first adjacent repetition"]
theorem domainRepeat_minimal {m : ℕ} {Delta : SimplexCategory}
    (f : SimplexCategory.mk (m + 1) ⟶ Delta)
    {i : Fin (m + 1)} (hi : domainRepeat? f = some i) :
    ∀ j : Fin (m + 1), j < i →
      f.toOrderHom j.castSucc ≠ f.toOrderHom j.succ := sorry

/-- The adjacent-repeat scan succeeds exactly for noninjective simplex morphisms. -/
@[simp, stacks 0G5N "adjacent repeated value existence criterion"]
theorem domainRepeat_isSome_iff {m : ℕ} {Delta : SimplexCategory}
    (f : SimplexCategory.mk (m + 1) ⟶ Delta) :
    (domainRepeat? f).isSome ↔ ¬Function.Injective f.toOrderHom := sorry

end Hom

/-- The deterministic factor after a codegeneracy at an adjacent repeated source value. -/
@[stacks 0G5N "deterministic codegeneracy factor"]
def factor_σ {m : ℕ} {Delta : SimplexCategory}
    (f : SimplexCategory.mk (m + 1) ⟶ Delta)
    (i : Fin (m + 1)) : SimplexCategory.mk m ⟶ Delta :=
  δ i.succ ≫ f

/-- Factoring at an adjacent repeated source value recovers the original simplex morphism. -/
@[reassoc, stacks 0G5N "codegeneracy factorization at an adjacent repetition"]
theorem factor_σ_spec {m : ℕ} {Delta : SimplexCategory}
    (f : SimplexCategory.mk (m + 1) ⟶ Delta)
    (i : Fin (m + 1)) (hi : f.toOrderHom i.castSucc = f.toOrderHom i.succ) :
    σ i ≫ factor_σ f i = f := sorry

/-- A typed word in coface and codegeneracy generators for a morphism from `⦋m⦌` to `⦋n⦌`. -/
@[stacks 0G5N "simplex generator words"]
inductive HomCode : (m n : ℕ) → Type
  /-- The empty generator word on an object. -/
  | id (n : ℕ) : HomCode n n
  /-- Append a coface generator to a typed word. -/
  | face {m n : ℕ} (i : Fin (n + 2)) (code : HomCode m n) : HomCode m (n + 1)
  /-- Prepend a codegeneracy generator to a typed word. -/
  | degeneracy {m n : ℕ} (i : Fin (m + 1)) (code : HomCode m n) : HomCode (m + 1) n

namespace HomCode

/-- Interpret a generator word as a morphism of skeletal simplex categories. -/
@[stacks 0G5N "generator word evaluation in the simplex category"]
def toHom : {m n : ℕ} → HomCode m n →
    (SimplexCategory.mk m ⟶ SimplexCategory.mk n)
  | _, _, .id _ => 𝟙 _
  | _, _, .face i code => code.toHom ≫ SimplexCategory.δ i
  | _, _, .degeneracy i code => SimplexCategory.σ i ≫ code.toHom

namespace Build

/-- The canonical word from the zero-dimensional simplex to a target dimension. -/
def fromZero : (n : ℕ) → HomCode 0 n
  | 0 => .id 0
  | n + 1 => .face 0 (fromZero n)

/-- The canonical fallback word from an arbitrary source to an arbitrary target. -/
def fallback : (m n : ℕ) → HomCode m n
  | 0, n => fromZero n
  | m + 1, n => .degeneracy 0 (fallback m n)

/-- A type-valued comparison which refines equal dimension indices definitionally. -/
inductive DimCmp : (m n : ℕ) → Type
  /-- The dimensions agree. -/
  | eq (n : ℕ) : DimCmp n n
  /-- The source dimension is strictly smaller. -/
  | lt {m n : ℕ} (h : m < n) : DimCmp m n
  /-- The target dimension is strictly smaller. -/
  | gt {m n : ℕ} (h : n < m) : DimCmp m n

/-- Lift a dimension comparison through one successor on each side. -/
def DimCmp.succ : {m n : ℕ} → DimCmp m n → DimCmp (m + 1) (n + 1)
  | _, _, .eq k => .eq (k + 1)
  | _, _, .lt h => .lt (Nat.succ_lt_succ h)
  | _, _, .gt h => .gt (Nat.succ_lt_succ h)

/-- Deterministically compare two dimensions while retaining their indexed relation. -/
def dimCmp : (m n : ℕ) → DimCmp m n
  | 0, 0 => .eq 0
  | 0, n + 1 => .lt (Nat.zero_lt_succ n)
  | m + 1, 0 => .gt (Nat.zero_lt_succ m)
  | m + 1, n + 1 => (dimCmp m n).succ

/-- Perform one deterministic same-successor recursion step from a dimension comparison. -/
def step
    (recur : {m n : ℕ} → (SimplexCategory.mk m ⟶ SimplexCategory.mk n) → HomCode m n) :
    {m n : ℕ} → DimCmp m n →
      (SimplexCategory.mk (m + 1) ⟶ SimplexCategory.mk (n + 1)) →
      HomCode (m + 1) (n + 1)
  | _, _, .eq k, f =>
      match Hom.domainRepeat? f with
      | some i => .degeneracy i (recur (SimplexCategory.factor_σ f i))
      | none => .id (k + 1)
  | _, _, .lt _, f =>
      let i := (Hom.targetGap? f).getD 0
      .face i (recur (SimplexCategory.factor_δ f i))
  | _, _, .gt _, f =>
      let i := (Hom.domainRepeat? f).getD 0
      .degeneracy i (recur (SimplexCategory.factor_σ f i))

/-- Fuel-bounded deterministic recursion underlying `ofHom`. -/
def run : (fuel m n : ℕ) →
    (SimplexCategory.mk m ⟶ SimplexCategory.mk n) → HomCode m n
  | 0, m, n, _ => fallback m n
  | _ + 1, 0, 0, _ => .id 0
  | fuel + 1, 0, n + 1, f =>
      let i := (Hom.targetGap? f).getD 0
      .face i (run fuel 0 n (SimplexCategory.factor_δ f i))
  | fuel + 1, m + 1, 0, f =>
      let i := (Hom.domainRepeat? f).getD 0
      .degeneracy i (run fuel m 0 (SimplexCategory.factor_σ f i))
  | fuel + 1, m + 1, n + 1, f =>
      step (fun {_ _} g ↦ run fuel _ _ g) (dimCmp m n) f

end Build

/-- Evaluate the deterministic builder with the canonical dimension fuel. -/
def build (m n : ℕ) (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n) : HomCode m n :=
  Build.run (m + n + 1) m n f

/-- A deterministic finite-ordinal generator code obtained by scanning for the first available
coface or codegeneracy factor at every recursive step. -/
@[stacks 0G5N "finite ordinal generator code"]
def ofHom (m n : ℕ) (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n) : HomCode m n :=
  build m n f

/-- The deterministic generator word evaluates back to the original simplex morphism. -/
theorem ofHom.toHom (m n : ℕ)
    (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    (ofHom m n f).toHom = f := sorry

end HomCode

/-- Rewrite a morphism in the opposite simplex category between its canonical skeletal
representatives. -/
@[stacks 0G5N "canonical simplex morphism representative"]
def canonicalHom {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') :
    SimplexCategory.mk Δ'.unop.len ⟶ SimplexCategory.mk Δ.unop.len :=
  eqToHom (SimplexCategory.mk_len Δ'.unop) ≫ θ.unop ≫
    eqToHom (SimplexCategory.mk_len Δ.unop).symm

end SimplexCategory
