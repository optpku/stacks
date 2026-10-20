/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.Pushforward

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 62.12.1: for a proper morphism `f : X' ⟶ X` of schemes locally of finite type
over a universally catenary base with dimension function `δ`, and a Gysin pair given by
an invertible module `ℒ` with section `s` (so `i = zeroSchemeι ℒ s` and
`D = zeroScheme ℒ s`), if the restriction of `ℒ` to `D` is trivial then cycle-level
Gysin commutes with proper pushforward along the cartesian square of
`zeroSchemePullbackOverHom f ℒ s`. -/
@[stacks 0H6D] #check
  (AlgebraicGeometry.Scheme.Modules.trivialGysin_map_eq_map_trivialGysin :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X X' : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    (f : X' ⟶ X) [IsProper f.left] (ℒ : X.left.Modules) [Invertible ℒ]
    (s : ℒ.sections)
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ))
    (k : ℤ) (α' : CycleGroup X'.left (X'.hom.relativeDimensionFunction δ) (k + 1)),
    trivialGysin X.hom δ ℒ s htriv k
        (CycleGroup.mapHom f.left (X'.hom.relativeDimensionFunction δ)
          (X.hom.relativeDimensionFunction δ) (k + 1) α') =
      CycleGroup.mapHom (zeroSchemePullbackOverHom f ℒ s).left
        ((zeroSchemeι ((pullback f.left).obj ℒ)
            (sectionsPullback f.left ℒ s) ≫ X'.hom).relativeDimensionFunction δ)
        ((zeroSchemeι ℒ s ≫ X.hom).relativeDimensionFunction δ) k
        (trivialGysin X'.hom δ ((pullback f.left).obj ℒ)
          (sectionsPullback f.left ℒ s)
          (isTrivial_zeroScheme_sectionsPullback f ℒ s htriv) k α'))

end AlgebraicGeometry.Scheme.Modules
