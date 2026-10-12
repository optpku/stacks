/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.CategoryTheory.Shift.ShiftedHom.ModuleCat
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_8_4_Linear

/-!
# Derived Ext over an affine base for algebraic spaces

A morphism `X ⟶ Spec A` of algebraic spaces equips shifted morphisms between derived
`𝒪_X`-modules with the `A`-module structure induced by the chartwise action of `A`.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open DerivedCategory.TStructure
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.DerivedExt

variable {A : Type u} [CommRing A]
variable {X : AlgebraicSpace (Spec (CommRingCat.of A))}

/-- The shifted-Hom bifunctor with its `A`-module structure induced by a morphism
`f : X ⟶ ofOver (Over.mk (𝟙 (Spec A)))`. -/
noncomputable def bifunctor
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) (n : ℤ) :
    (ModuleDerived X)ᵒᵖ ⥤ ModuleDerived X ⥤ ModuleCat.{u + 1} A :=
  @CategoryTheory.ShiftedHom.linearCoyoneda A _
    (ModuleDerived X) _ _
    (@DerivedCategory.instLinear A _ (Modules X) _ _
      (Modules.baseLinear f) _)
    _ n

/-- The `A`-module of degree-`n` derived extensions from `K` to `L`, with scalar action
induced by `f`. -/
noncomputable abbrev value
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (K L : ModuleDerived X) (n : ℤ) : ModuleCat.{u + 1} A :=
  ((bifunctor f n).obj (op K)).obj L

/-- Forgetting the `A`-action on `value f K L n` recovers the shifted-morphism group
`Ext⁽n⁾(K, L)`. -/
theorem value_forget
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
    (K L : ModuleDerived X) (n : ℤ) :
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).obj (value f K L n) =
      AddCommGrpCat.of (Ext⁽n⁾(K, L)) :=
  sorry

variable [IsNoetherianRing A]

/-- If `X` is proper over a Noetherian affine scheme, then the `A`-module of degree-`n`
derived extensions from a bounded-above complex with coherent cohomology to a bounded-below
complex with coherent cohomology is finite. -/
@[stacks 0D0T]
theorem finite
    (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) [Proper f]
    (K L : ModuleDerived X)
    (hK_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X)) K)
    (hK_boundedAbove :
      (t.minus : ObjectProperty (ModuleDerived X)) K)
    (hL_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent (structureSheaf X)) L)
    (hL_boundedBelow :
      (t.plus : ObjectProperty (ModuleDerived X)) L)
    (n : ℤ) :
    Module.Finite A (value f K L n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.DerivedExt
