/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.Algebra.Category.ModuleCat.Determinant.Prod
public import ReasLib.Algebra.Category.ModuleCat.ShortComplex
import Mathlib.Tactic.CrossRefAttribute

/-!
# Determinants of short exact sequences in `ModuleCat`

A splitting identifies the middle term with the concrete product of the two endpoints via the
shared `ShortComplex.Splitting.prodIso`.  The determinant comparison morphism is therefore
explicit: first apply the determinant product morphism, then transport the resulting determinant
along this product-to-middle isomorphism.  For a short exact sequence with projective target,
Mathlib's projective splitting supplies the splitting data.
@stack 0FJB
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct Module.Determinant

universe u v

namespace ModuleCat.Determinant

variable (R : Type u) [CommRing R]
variable {S : ShortComplex (ModuleCat.{v} R)}

/-- The determinant comparison morphism determined by a splitting. -/
@[stacks 0FJB "determinant morphism from a splitting"]
def splitHom (s : S.Splitting) :
    ModuleCat.TensorProduct.obj R (obj R S.X₁) (obj R S.X₃) ⟶ obj R S.X₂ :=
  prodHom R S.X₁ S.X₃ ≫ (mapIso R s.prodIso).hom

/-- After the determinant inclusion, the splitting comparison factors through the concrete
product determinant and the induced ambient exterior-algebra isomorphism. -/
@[reassoc, stacks 0FJB "ambient formula for the determinant morphism from a splitting"]
theorem splitHom_ι (s : S.Splitting) :
    splitHom R s ≫ ι R S.X₂ =
      prodHom R S.X₁ S.X₃ ≫ ι R (ModuleCat.of R (S.X₁ × S.X₃)) ≫
        (ambientIso R s.prodIso).hom := sorry

/-- On a pure tensor, the determinant morphism of a splitting wedges the image from the left
term with the image under the chosen section of the right term. -/
@[simp, stacks 0FJB "pure tensor formula for a split determinant morphism"]
theorem ι_splitHom_tmul (s : S.Splitting)
    (x₁ : det[R](S.X₁)) (x₃ : det[R](S.X₃)) :
    ι R S.X₂ (splitHom R s (x₁ ⊗ₜ[R] x₃)) =
      ExteriorAlgebra.map S.f.hom (x₁ : ExteriorAlgebra R S.X₁) *
        ExteriorAlgebra.map s.s.hom (x₃ : ExteriorAlgebra R S.X₃) := sorry

/-- The determinant morphism constructed from a splitting does not depend on the chosen
splitting. -/
@[stacks 0FJB "independence of the determinant morphism from a splitting"]
theorem splitHom_independent (s t : S.Splitting) :
    splitHom R s = splitHom R t := sorry

/-- The determinant morphism of a splitting is an isomorphism.  This declaration records only
the property and does not manufacture inverse data from its placeholder proof. -/
@[stacks 0FJB "split determinant morphism is an isomorphism"]
instance splitHom_isIso (s : S.Splitting)
    [Module.Finite R S.X₁] [Module.Projective R S.X₁]
    [Module.Finite R S.X₃] [Module.Projective R S.X₃] :
    IsIso (splitHom R s) := sorry

/-- The canonical forward determinant morphism of a short exact sequence with projective target,
constructed from Mathlib's projective splitting. -/
@[stacks 0FJB "determinant morphism of a short exact sequence"]
def exactHom (hS : S.ShortExact) [Projective S.X₃] :
    ModuleCat.TensorProduct.obj R (obj R S.X₁) (obj R S.X₃) ⟶ obj R S.X₂ :=
  splitHom R hS.splittingOfProjective

/-- The canonical short-exact determinant morphism agrees with the morphism from every chosen
splitting. -/
@[stacks 0FJB "split description of the short-exact determinant morphism"]
theorem exactHom_eq_splitHom (hS : S.ShortExact) (s : S.Splitting)
    [Projective S.X₃] :
    exactHom R hS = splitHom R s := sorry

/-- Wedge-and-lift characterization of the determinant morphism of a short exact sequence: any
exterior-algebra lift of the right determinant element gives the same wedge with the left
determinant element. -/
@[stacks 0FJB "wedge and lift formula for a short-exact determinant morphism"]
theorem ι_exactHom_tmul_of_lift (hS : S.ShortExact)
    [Projective S.X₃]
    (x₁ : det[R](S.X₁)) (x₃ : det[R](S.X₃)) (y₃ : ExteriorAlgebra R S.X₂)
    (hy₃ : ExteriorAlgebra.map S.g.hom y₃ = (x₃ : ExteriorAlgebra R S.X₃)) :
    ι R S.X₂ (exactHom R hS (x₁ ⊗ₜ[R] x₃)) =
      ExteriorAlgebra.map S.f.hom (x₁ : ExteriorAlgebra R S.X₁) * y₃ := sorry

/-- The canonical determinant morphism of a short exact sequence is an isomorphism.  This is a
property statement only; it is not used here to define an inverse or an isomorphism. -/
@[stacks 0FJB "short-exact determinant morphism is an isomorphism"]
instance exactHom_isIso (hS : S.ShortExact)
    [Module.Finite R S.X₁] [Module.Projective R S.X₁]
    [Module.Finite R S.X₃] [Module.Projective R S.X₃] :
    IsIso (exactHom R hS) := sorry

end ModuleCat.Determinant
