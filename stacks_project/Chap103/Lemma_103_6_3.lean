module

public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap96.Definition_96_12_1_LocallyQuasicoherent
public import stacks_project.Chap96.Lemma_96_11_2_Pullback
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation

/-!
# Detection of local quasi-coherence on an fppf covering of algebraic stacks

On an algebraic stack, local quasi-coherence of an fppf module is detected
on a jointly point-covering family of flat and locally finitely presented
morphisms of algebraic stacks.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicStack AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- Lemma 103.6.3: let `X` be an algebraic stack. Let `f j : Xj j ⟶ X` be a family
of flat and locally finitely presented morphisms of algebraic stacks with
`|X| = ⋃ |f j|(|Xj j|)`. Let `F` be a sheaf of `𝒪_X`-modules on `X_fppf`. If each
inverse image `(modulePullback (f j)).obj F` is locally quasi-coherent, then so
is `F`. -/
@[stacks 07AP]
theorem isLocallyQuasicoherent_of_fppfCovering
    {J : Type v} {Xj : J → GroupoidsOver S} [∀ j, AlgebraicStack (Xj j)]
    (f : ∀ j, Xj j ⟶ X) [∀ j, Flat (f j)] [∀ j, LocallyOfFinitePresentation (f j)]
    (h_cover : ∀ x : Points X, ∃ j, x ∈ Set.range (Points.map (f j)))
    (F : SheafOfModules.{u} (structureSheaf X))
    (h_lqc : ∀ j, IsLocallyQuasicoherent ((modulePullback (f j)).obj F).val) :
    IsLocallyQuasicoherent F.val :=
  sorry

/-- If `f : Y ⟶ X` is a flat and locally finitely presented morphism of algebraic
stacks which is surjective on points, then an fppf `𝒪_X`-module is locally
quasi-coherent as soon as its inverse image along `f` is. -/
theorem isLocallyQuasicoherent_of_fppf_pointsSurjective
    {Y : GroupoidsOver S} [AlgebraicStack Y] (f : Y ⟶ X)
    [Flat f] [LocallyOfFinitePresentation f]
    (h_cover : Function.Surjective (Points.map f))
    (F : SheafOfModules.{u} (structureSheaf X))
    (h_lqc : IsLocallyQuasicoherent ((modulePullback f).obj F).val) :
    IsLocallyQuasicoherent F.val :=
  sorry

end AlgebraicGeometry.AlgebraicStack
