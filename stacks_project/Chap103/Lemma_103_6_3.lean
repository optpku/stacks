module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.LocallyQuasicoherent.Descent
import StacksCheckRecall

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

/- Lemma 103.6.3: let `X` be an algebraic stack. Let `f j : Xj j ⟶ X` be a family
of flat and locally finitely presented morphisms of algebraic stacks with
`|X| = ⋃ |f j|(|Xj j|)`. Let `F` be a sheaf of `𝒪_X`-modules on `X_fppf`. If each
inverse image `(modulePullback (f j)).obj F` is locally quasi-coherent, then so
is `F`. -/
@[stacks 07AP] #check
  (AlgebraicGeometry.AlgebraicStack.isLocallyQuasicoherent_of_fppfCovering :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {J : Type v} {Xj : J → GroupoidsOver S} [∀ j, AlgebraicStack (Xj j)]
    (f : ∀ j, Xj j ⟶ X) [∀ j, Flat (f j)] [∀ j, LocallyOfFinitePresentation (f j)]
    (h_cover : ∀ x : Points X, ∃ j, x ∈ Set.range (Points.map (f j)))
    (F : SheafOfModules.{u} (structureSheaf X))
    (h_lqc : ∀ j, IsLocallyQuasicoherent ((modulePullback (f j)).obj F).val),
    IsLocallyQuasicoherent F.val)

/- If `f : Y ⟶ X` is a flat and locally finitely presented morphism of algebraic
stacks which is surjective on points, then an fppf `𝒪_X`-module is locally
quasi-coherent as soon as its inverse image along `f` is. -/
#check (AlgebraicGeometry.AlgebraicStack.isLocallyQuasicoherent_of_fppf_pointsSurjective :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Y : GroupoidsOver S} [AlgebraicStack Y] (f : Y ⟶ X)
    [Flat f] [LocallyOfFinitePresentation f]
    (h_cover : Function.Surjective (Points.map f))
    (F : SheafOfModules.{u} (structureSheaf X))
    (h_lqc : IsLocallyQuasicoherent ((modulePullback f).obj F).val),
    IsLocallyQuasicoherent F.val)
