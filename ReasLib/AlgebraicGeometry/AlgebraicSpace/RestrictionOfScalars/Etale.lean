/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars.Map
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree.Basic

/-!
# Étale and surjective restriction of scalars

If `X' ⟶ X` is étale and `Z ⟶ B` is finite locally free, the induced map
`Res_{Z/B}(X') ⟶ Res_{Z/B}(X)` is representable by algebraic spaces and étale,
and is surjective when `X' ⟶ X` is also surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom renaming Etale → GroupoidEtale
open AlgebraicGeometry.Groupoids.Hom renaming Surjective → GroupoidSurjective
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars

/-- Let `S` be a scheme and let `X' ⟶ X ⟶ Z ⟶ B` be morphisms
of algebraic spaces over `S`. If `h : X' ⟶ X` is étale and `g : Z ⟶ B` is finite
locally free, then `mapGroupoids h f g : toGroupoids (h ≫ f) g ⟶ toGroupoids f g`
is representable by algebraic spaces and étale. -/
@[stacks 05YD, instance]
instance instEtale_map {S : Scheme.{u}} {X' X Z B : AlgebraicSpace S}
    (h : X' ⟶ X) (f : X ⟶ Z) (g : Z ⟶ B)
    [AlgebraicSpace.Etale h] [FiniteLocallyFree g] :
    GroupoidEtale (mapGroupoids h f g) :=
  sorry

/-- Let `S` be a scheme and let `X' ⟶ X ⟶ Z ⟶ B` be morphisms
of algebraic spaces over `S`. If `h : X' ⟶ X` is étale and surjective and
`g : Z ⟶ B` is finite locally free, then
`mapGroupoids h f g : toGroupoids (h ≫ f) g ⟶ toGroupoids f g` is surjective. -/
@[stacks 05YD, instance]
instance instSurjective_map {S : Scheme.{u}} {X' X Z B : AlgebraicSpace S}
    (h : X' ⟶ X) (f : X ⟶ Z) (g : Z ⟶ B)
    [AlgebraicSpace.Etale h] [AlgebraicSpace.Surjective h] [FiniteLocallyFree g] :
    GroupoidSurjective (mapGroupoids h f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars
