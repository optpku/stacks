module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Proper morphisms from finite coproducts

A morphism induced from a finite coproduct is proper when every component morphism is proper.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- A morphism from a finite coproduct is proper if every component morphism is proper. -/
theorem proper_sigma_desc {ι : Type u} {X : ι → Scheme.{u}} {Y : Scheme.{u}}
    (f : ∀ i, X i ⟶ Y) [Finite ι] (hf : ∀ i, IsProper (f i)) :
    IsProper (Sigma.desc f) := sorry

/-- The morphism from a finite coproduct induced by proper morphisms is proper. -/
instance instIsProperSigmaDesc {ι : Type u} {X : ι → Scheme.{u}} {Y : Scheme.{u}}
    (f : ∀ i, X i ⟶ Y) [Finite ι] [∀ i, IsProper (f i)] :
    IsProper (Sigma.desc f) :=
  proper_sigma_desc f (fun i ↦ show IsProper (f i) from inferInstance)

end AlgebraicGeometry
