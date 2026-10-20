module

public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap103.Lemma_103_5_1_Rule

/-!
# Higher direct images of types of modules on algebraic stacks

For a quasi-compact quasi-separated morphism of algebraic stacks, étale
higher direct images preserve any étale-module rule.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 103.5.1: let `M` be a rule associating to every algebraic stack `X` a
weak Serre subcategory `M.predicate X` of étale `𝒪_X`-modules, stable under
inverse image along smooth morphisms, detected on jointly point-covering
smooth families, and stable under `R^i f_*` when source and target are
representable by affine schemes. Then for every quasi-compact and
quasi-separated morphism `f : X ⟶ Y` of algebraic stacks, the étale higher
direct image functor `R^i f_*` sends `M.predicate X` into `M.predicate Y`. -/
@[stacks 076Z]
theorem mapsHigherDirectImage {S : Scheme.{u}} (M : EtaleModuleRule S)
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (i : ℕ) :
    M.predicate X ≤ (M.predicate Y).inverseImage (higherDirectImageFunctor f i) :=
  sorry

/-- Membership form of étale higher-direct-image stability along a
quasi-compact quasi-separated morphism of algebraic stacks. -/
theorem mem_higherDirectImage {S : Scheme.{u}} (M : EtaleModuleRule S)
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (i : ℕ)
    {F : etaleModules X} (hF : M.predicate X F) :
    M.predicate Y ((higherDirectImageFunctor f i).obj F) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
