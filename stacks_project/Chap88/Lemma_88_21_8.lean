/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_20_1_Etale
public import stacks_project.Chap88.Definition_88_21_1

/-!
# Étale-locality of rig-surjectivity on the target

Rig-surjectivity of a locally finite-type morphism of locally Noetherian
formal algebraic spaces may be checked after base change along an étale
covering family of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FormalAlgebraicSpace
  CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective

/-- Lemma 88.21.8: let `S` be a scheme, and let `f : X ⟶ Y` be a morphism of
locally Noetherian formal algebraic spaces which is locally of finite type.
Let `{g i : Y_ i ⟶ Y}` be a family of morphisms of formal algebraic spaces
which are representable by algebraic spaces and étale, such that the coproduct
`sigmaDesc g` is surjective. Then `f` is `RigSurjective` if and only if each
base change `pullback.snd f (g i) : X ×_Y Y_ i ⟶ Y_ i` is `RigSurjective`. -/
@[stacks 0AQV]
theorem iff_etaleCover {S : Scheme.{u}} {ι : Type u}
    {X Y : (Over S)ᵒᵖ ⥤ Type u} {Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [∀ i, IsFormalAlgebraicSpace (Y_ i)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [∀ i, IsLocallyNoetherian (Y_ i)]
    (f : X ⟶ Y) (g : ∀ i, Y_ i ⟶ Y)
    [LocallyOfFiniteType f] [∀ i, Etale (g i)]
    [∀ i, HasPullback f (g i)]
    [∀ i, IsFormalAlgebraicSpace (pullback f (g i))]
    [∀ i, IsLocallyNoetherian (pullback f (g i))]
    [∀ i, LocallyOfFiniteType (pullback.snd f (g i))]
    (h_cover :
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc g)) :
    RigSurjective f ↔ ∀ i, RigSurjective (pullback.snd f (g i)) :=
  sorry

/-- If each base change `pullback.snd f (g i)` along an étale covering family
`g` with fppf-locally surjective coproduct `sigmaDesc g` is `RigSurjective`,
then `f` is `RigSurjective`. -/
theorem of_etaleCover {S : Scheme.{u}} {ι : Type u}
    {X Y : (Over S)ᵒᵖ ⥤ Type u} {Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [∀ i, IsFormalAlgebraicSpace (Y_ i)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [∀ i, IsLocallyNoetherian (Y_ i)]
    (f : X ⟶ Y) (g : ∀ i, Y_ i ⟶ Y)
    [LocallyOfFiniteType f] [∀ i, Etale (g i)]
    [∀ i, HasPullback f (g i)]
    [∀ i, IsFormalAlgebraicSpace (pullback f (g i))]
    [∀ i, IsLocallyNoetherian (pullback f (g i))]
    [∀ i, LocallyOfFiniteType (pullback.snd f (g i))]
    (h_cover :
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc g))
    (h : ∀ i, RigSurjective (pullback.snd f (g i))) :
    RigSurjective f :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective
