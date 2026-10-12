/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Bifunctor
public import ReasLib.Algebra.Category.ModuleCat.TensorProduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor products of module-valued cochain complexes

This file totalizes the universe-polymorphic tensor bifunctor for modules.  Unlike the monoidal
tensor product on `ModuleCat`, neither input complex is required to have the carrier universe of
the base ring.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace CochainComplex.TensorProduct

variable {R : Type u} [CommRing R]

/-- The existence of the total tensor product of two module-valued cochain complexes. -/
abbrev HasTotal (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (L : CochainComplex (ModuleCat.{w} R) ℤ) : Prop :=
  HomologicalComplex.HasMapBifunctor K L
    (ModuleCat.TensorProduct.functor.{u, v, w} R) (ComplexShape.up ℤ)

/-- The total tensor product of two module-valued cochain complexes in possibly different
carrier universes. -/
@[stacks 09LL "total tensor product of module-valued cochain complexes"]
noncomputable abbrev obj (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (L : CochainComplex (ModuleCat.{w} R) ℤ) [HasTotal K L] :
    CochainComplex (ModuleCat.{max v w} R) ℤ :=
  HomologicalComplex.mapBifunctor K L
    (ModuleCat.TensorProduct.functor.{u, v, w} R) (ComplexShape.up ℤ)

end CochainComplex.TensorProduct
