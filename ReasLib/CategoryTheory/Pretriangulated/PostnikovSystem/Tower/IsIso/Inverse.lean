/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Iso.Explicit
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.IsIso.Basic

/-!
# Explicit Inverses of Sequential Postnikov-Tower Morphisms

This file constructs an inverse and an isomorphism from explicit componentwise
invertibility certificates, without local instance installation.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Tower

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ k : ℤ, Functor.Additive (shiftFunctor D k)] [Pretriangulated D]
variable {T T' : Tower D}

/-- Compatibility of the inverse row-object components with the tower differential. -/
@[stacks 0D8Z]
theorem inverse_comm_d (f : T ⟶ T') (hx : ∀ n, IsIso (f.xMap n)) (n : ℕ) :
    CommSq (T'.d n) (hx (n + 1)).toIso.inv
      (hx n).toIso.inv (T.d n) := sorry

/-- Compatibility of the inverse components with the comparison to the row object. -/
@[stacks 0D8Z]
theorem inverse_comm_toX (f : T ⟶ T') (hx : ∀ n, IsIso (f.xMap n))
    (hy : ∀ n, IsIso (f.yMap n)) (n : ℕ) :
    CommSq (T'.toX n) (hy n).toIso.inv
      (hx n).toIso.inv (T.toX n) := sorry

/-- Compatibility of the inverse components with the second map of a stage triangle. -/
@[stacks 0D8Z]
theorem inverse_comm_toNext (f : T ⟶ T') (hx : ∀ n, IsIso (f.xMap n))
    (hy : ∀ n, IsIso (f.yMap n)) (n : ℕ) :
    CommSq (T'.toNext n) (hx (n + 1)).toIso.inv
      (hy n).toIso.inv (T.toNext n) := sorry

/-- Compatibility of the inverse auxiliary components with the connecting map. -/
@[stacks 0D8Z]
theorem inverse_comm_connecting (f : T ⟶ T') (hy : ∀ n, IsIso (f.yMap n)) (n : ℕ) :
    CommSq (T'.connecting n) (hy n).toIso.inv
      (((hy (n + 1)).toIso.inv)⟦(1 : ℤ)⟧')
      (T.connecting n) := sorry

/-- The componentwise inverse of a sequential Postnikov-tower morphism. Invertibility
certificates are explicit inputs, so callers do not need local instance plumbing. -/
@[stacks 0D8Z "componentwise inverse of a Postnikov-tower morphism"]
noncomputable def inverse (f : T ⟶ T') (hx : ∀ n, IsIso (f.xMap n))
    (hy : ∀ n, IsIso (f.yMap n)) : T' ⟶ T where
  xMap n := (hx n).toIso.inv
  yMap n := (hy n).toIso.inv
  comm_d := inverse_comm_d f hx
  comm_toX := inverse_comm_toX f hx hy
  comm_toNext := inverse_comm_toNext f hx hy
  comm_connecting := inverse_comm_connecting f hy

/-- A row-object component of the componentwise inverse is the corresponding inverse map. -/
@[simp, stacks 0D8Z]
theorem inverse_xMap (f : T ⟶ T') (hx : ∀ n, IsIso (f.xMap n))
    (hy : ∀ n, IsIso (f.yMap n)) (n : ℕ) :
    (inverse f hx hy).xMap n = (hx n).toIso.inv := sorry

/-- An auxiliary-object component of the componentwise inverse is the corresponding inverse map. -/
@[simp, stacks 0D8Z]
theorem inverse_yMap (f : T ⟶ T') (hx : ∀ n, IsIso (f.xMap n))
    (hy : ∀ n, IsIso (f.yMap n)) (n : ℕ) :
    (inverse f hx hy).yMap n = (hy n).toIso.inv := sorry

/-- A tower morphism followed by its componentwise inverse is the identity. -/
@[simp, stacks 0D8Z]
theorem hom_inverse_id (f : T ⟶ T') (hx : ∀ n, IsIso (f.xMap n))
    (hy : ∀ n, IsIso (f.yMap n)) : f ≫ inverse f hx hy = 𝟙 T := sorry

/-- The componentwise inverse followed by the original tower morphism is the identity. -/
@[simp, stacks 0D8Z]
theorem inverse_hom_id (f : T ⟶ T') (hx : ∀ n, IsIso (f.xMap n))
    (hy : ∀ n, IsIso (f.yMap n)) : inverse f hx hy ≫ f = 𝟙 T' := sorry

/-- Assemble an isomorphism of sequential Postnikov towers from componentwise invertibility. -/
@[stacks 0D8Z "componentwise isomorphism of sequential Postnikov towers"]
noncomputable def isoOfComponents (f : T ⟶ T') (hx : ∀ n, IsIso (f.xMap n))
    (hy : ∀ n, IsIso (f.yMap n)) : T ≅ T' where
  hom := f
  inv := inverse f hx hy
  hom_inv_id := hom_inverse_id f hx hy
  inv_hom_id := inverse_hom_id f hx hy

/-- The forward map of `isoOfComponents` is the supplied tower morphism. -/
@[simp, stacks 0D8Z]
theorem isoOfComponents_hom (f : T ⟶ T') (hx : ∀ n, IsIso (f.xMap n))
    (hy : ∀ n, IsIso (f.yMap n)) : (isoOfComponents f hx hy).hom = f := sorry

/-- The inverse map of `isoOfComponents` is the explicit componentwise inverse. -/
@[simp, stacks 0D8Z]
theorem isoOfComponents_inv (f : T ⟶ T') (hx : ∀ n, IsIso (f.xMap n))
    (hy : ∀ n, IsIso (f.yMap n)) :
    (isoOfComponents f hx hy).inv = inverse f hx hy := sorry

/-- Componentwise invertibility implies invertibility in the category of sequential Postnikov
towers. This is a theorem rather than a global instance, avoiding a typeclass loop. -/
@[stacks 0D8Z]
theorem isIso_of_components (f : T ⟶ T') (hx : ∀ n, IsIso (f.xMap n))
    (hy : ∀ n, IsIso (f.yMap n)) : IsIso f := sorry

/-- Levelwise invertibility implies invertibility in the category of sequential Postnikov
towers. -/
@[stacks 0D8Z]
theorem isIso_of_levelwise (f : T ⟶ T') (hf : f.IsLevelwiseIso) : IsIso f := sorry

end CategoryTheory.PostnikovSystem.Tower
