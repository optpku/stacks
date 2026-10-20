/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSurjective
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.Etale

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

/-- A locally finite-type morphism of locally Noetherian formal algebraic
spaces is rig-surjective if and only if all its base changes along a family
of representable étale morphisms with fppf-locally surjective coproduct are
rig-surjective. -/
theorem iff_etaleCover {S : Scheme.{u}} {ι : Type u}
    {X Y : (Over S)ᵒᵖ ⥤ Type u} {Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [∀ i, IsFormalAlgebraicSpace (Y_ i)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [∀ i, IsLocallyNoetherian (Y_ i)]
    (f : X ⟶ Y) (g : ∀ i, Y_ i ⟶ Y)
    [LocallyOfFiniteType f] [∀ i, Etale (g i)]
    (h_cover :
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc g)) :
    RigSurjective f ↔ ∀ i, RigSurjective (pullback.snd f (g i)) :=
  sorry

/-- If each base change of a locally finite-type morphism of locally
Noetherian formal algebraic spaces along a representable étale covering
family with fppf-locally surjective coproduct is rig-surjective, then the
original morphism is rig-surjective. -/
theorem of_etaleCover {S : Scheme.{u}} {ι : Type u}
    {X Y : (Over S)ᵒᵖ ⥤ Type u} {Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [∀ i, IsFormalAlgebraicSpace (Y_ i)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [∀ i, IsLocallyNoetherian (Y_ i)]
    (f : X ⟶ Y) (g : ∀ i, Y_ i ⟶ Y)
    [LocallyOfFiniteType f] [∀ i, Etale (g i)]
    (h_cover :
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc g))
    (h : ∀ i, RigSurjective (pullback.snd f (g i))) :
    RigSurjective f :=
  (iff_etaleCover f g h_cover).mpr h

end AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective
