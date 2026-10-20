/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSurjective.EtaleLocal
import StacksCheckRecall

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

/- Lemma 88.21.8: let `S` be a scheme, and let `f : X ⟶ Y` be a morphism of
locally Noetherian formal algebraic spaces which is locally of finite type.
Let `{g i : Y_ i ⟶ Y}` be a family of morphisms of formal algebraic spaces
which are representable by algebraic spaces and étale, such that the coproduct
`sigmaDesc g` is surjective. Then `f` is `RigSurjective` if and only if each
base change `pullback.snd f (g i) : X ×_Y Y_ i ⟶ Y_ i` is `RigSurjective`. -/
@[stacks 0AQV]
#check (AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective.iff_etaleCover :
  ∀ {S : Scheme.{u}} {ι : Type u}
    {X Y : (Over S)ᵒᵖ ⥤ Type u} {Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [∀ i, IsFormalAlgebraicSpace (Y_ i)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [∀ i, IsLocallyNoetherian (Y_ i)]
    (f : X ⟶ Y) (g : ∀ i, Y_ i ⟶ Y)
    [LocallyOfFiniteType f] [∀ i, Etale (g i)]
    (h_cover :
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc g)),
    RigSurjective f ↔ ∀ i, RigSurjective (pullback.snd f (g i)))

#check (AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective.of_etaleCover :
  ∀ {S : Scheme.{u}} {ι : Type u}
    {X Y : (Over S)ᵒᵖ ⥤ Type u} {Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [∀ i, IsFormalAlgebraicSpace (Y_ i)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [∀ i, IsLocallyNoetherian (Y_ i)]
    (f : X ⟶ Y) (g : ∀ i, Y_ i ⟶ Y)
    [LocallyOfFiniteType f] [∀ i, Etale (g i)]
    (h_cover :
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc g))
    (h : ∀ i, RigSurjective (pullback.snd f (g i))),
    RigSurjective f)
