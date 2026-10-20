/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import stacks_project.Chap96.Lemma_96_12_5_Comparison
public import stacks_project.Chap96.Lemma_96_15_1_Abelian
public import stacks_project.Chap103.Lemma_103_9_2

/-!
# Exactness of quasi-coherent complexes versus parasitic homology

On an algebraic stack, exactness of a composite-zero pair in `QCoh(𝒪_X)` is
equivalent to the associated homology `Ker(β)/Im(α)` being parasitic when that
homology is computed in `Mod(X_τ, 𝒪_X)` for `τ` étale or fppf.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

variable {S : Scheme.{u}}

/-- Transport of a short complex of quasi-coherent modules to `Mod(X_τ, 𝒪_X)`. -/
def toAssociatedShortComplex (X : GroupoidsOver S) (τ : StandardTopology)
    (sc : ShortComplex (QCoh X)) : ShortComplex (associatedModules X τ) where
  f := (toAssociatedModules X τ).map sc.f
  g := (toAssociatedModules X τ).map sc.g
  zero := sorry

/-- The first map of `toAssociatedShortComplex` is the image of `sc.f`. -/
theorem toAssociatedShortComplex_f (X : GroupoidsOver S) (τ : StandardTopology)
    (sc : ShortComplex (QCoh X)) :
    (toAssociatedShortComplex X τ sc).f = (toAssociatedModules X τ).map sc.f :=
  sorry

/-- The second map of `toAssociatedShortComplex` is the image of `sc.g`. -/
theorem toAssociatedShortComplex_g (X : GroupoidsOver S) (τ : StandardTopology)
    (sc : ShortComplex (QCoh X)) :
    (toAssociatedShortComplex X τ sc).g = (toAssociatedModules X τ).map sc.g :=
  sorry

/-- The homology `Ker(β)/Im(α)` of a quasi-coherent complex, computed in
`Mod(X_τ, 𝒪_X)`. -/
def associatedHomology (X : GroupoidsOver S) (τ : StandardTopology)
    (sc : ShortComplex (QCoh X)) : associatedModules X τ :=
  (toAssociatedShortComplex X τ sc).homology

/-- `associatedHomology` is the homology of the transported short complex. -/
theorem associatedHomology_eq (X : GroupoidsOver S) (τ : StandardTopology)
    (sc : ShortComplex (QCoh X)) :
    associatedHomology X τ sc = (toAssociatedShortComplex X τ sc).homology :=
  sorry

/-- Parasitic vanishing of associated homology is membership in
`associatedModules.parasitic`. -/
theorem associatedHomology_isParasitic_iff {X : GroupoidsOver S} [AlgebraicStack X]
    (τ : StandardTopology) (sc : ShortComplex (QCoh X)) :
    IsParasitic (associatedModulePresheaf (associatedHomology X τ sc)) ↔
      associatedModules.parasitic X τ (associatedHomology X τ sc) :=
  sorry

/-- Lemma 103.9.4: let `X` be an algebraic stack. Let `α : F ⟶ G` and
`β : G ⟶ H` be maps in `QCoh(𝒪_X)` with `β ∘ α = 0`. The following are
equivalent: in the abelian category `QCoh(𝒪_X)` the complex `F ⟶ G ⟶ H` is
exact at `G`, and `Ker(β)/Im(α)` computed in either `Mod(X_étale, 𝒪_X)` or
`Mod(X_fppf, 𝒪_X)` is parasitic. -/
@[stacks 0776]
theorem exact_iff_homology_isParasitic {X : GroupoidsOver S} [AlgebraicStack X]
    {F G H : QCoh X} (α : F ⟶ G) (β : G ⟶ H) (h : α ≫ β = 0)
    {τ : StandardTopology} (hτ : τ = .etale ∨ τ = .fppf) :
    (ShortComplex.mk α β h).Exact ↔
      IsParasitic (associatedModulePresheaf
        (associatedHomology X τ (ShortComplex.mk α β h))) :=
  sorry

/-- Exactness in `QCoh(𝒪_X)` is equivalent to parasitic associated homology in
the étale topology. -/
theorem exact_iff_homology_isParasitic_etale {X : GroupoidsOver S}
    [AlgebraicStack X] {F G H : QCoh X} (α : F ⟶ G) (β : G ⟶ H)
    (h : α ≫ β = 0) :
    (ShortComplex.mk α β h).Exact ↔
      IsParasitic (associatedModulePresheaf
        (associatedHomology X .etale (ShortComplex.mk α β h))) :=
  sorry

/-- Exactness in `QCoh(𝒪_X)` is equivalent to parasitic associated homology in
the fppf topology. -/
theorem exact_iff_homology_isParasitic_fppf {X : GroupoidsOver S}
    [AlgebraicStack X] {F G H : QCoh X} (α : F ⟶ G) (β : G ⟶ H)
    (h : α ≫ β = 0) :
    (ShortComplex.mk α β h).Exact ↔
      IsParasitic (associatedModulePresheaf
        (associatedHomology X .fppf (ShortComplex.mk α β h))) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.QCoh
