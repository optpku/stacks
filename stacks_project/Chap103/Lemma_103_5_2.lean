module

public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap103.Lemma_103_5_2_Rule

/-!
# Higher direct images of types of modules on algebraic stacks

For a quasi-compact quasi-separated morphism of algebraic stacks, fppf
higher direct images preserve any fppf-module rule.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 103.5.2: let `M` be a rule associating to every algebraic stack `X` a
weak Serre subcategory `M.predicate X` of fppf `𝒪_X`-modules, stable under
inverse image along smooth morphisms, detected on jointly point-covering
smooth families, and stable under `R^i f_*` when source and target are
representable by affine schemes. Then for every quasi-compact and
quasi-separated morphism `f : X ⟶ Y` of algebraic stacks, the fppf higher
direct image functor `R^i f_*` sends `M.predicate X` into `M.predicate Y`. -/
@[stacks 0770]
theorem mapsHigherDirectImage {S : Scheme.{u}} (M : FppfModuleRule S)
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (i : ℕ) :
    M.predicate X ≤ (M.predicate Y).inverseImage (fppfHigherDirectImageFunctor f i) :=
  sorry

/-- Membership form of fppf higher-direct-image stability along a
quasi-compact quasi-separated morphism of algebraic stacks. -/
theorem mem_higherDirectImage {S : Scheme.{u}} (M : FppfModuleRule S)
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (i : ℕ)
    {F : fppfModules X} (hF : M.predicate X F) :
    M.predicate Y ((fppfHigherDirectImageFunctor f i).obj F) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
