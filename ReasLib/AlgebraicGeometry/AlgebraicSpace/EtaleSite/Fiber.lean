/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Spaces
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Fibre objects in the spaces-étale site

The fibre product of two objects over a third is structured over the base algebraic space
by its first projection.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The fibre product `U ×_W V` as an object of `X_spaces,étale`, structured over `X`
by `pullback.fst j.left f.left ≫ U.hom`. -/
noncomputable abbrev spacesEtaleSite.fiber {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U V W : spacesEtaleSite X} (j : U ⟶ W) (f : V ⟶ W) [Etale f.left] :
    spacesEtaleSite X :=
  MorphismProperty.Over.mk ⊤ (pullback.fst j.left f.left ≫ U.hom)
    (@Etale.etale_comp S (pullback j.left f.left) U.left
      (pullback.fst j.left f.left) X U.hom
      (Etale.pullback_fst j.left inferInstance) U.prop)

/-- The underlying algebraic space of `spacesEtaleSite.fiber j f` is the fibre product
of `j.left` and `f.left`. -/
@[simp]
theorem spacesEtaleSite.fiber_left {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U V W : spacesEtaleSite X} (j : U ⟶ W) (f : V ⟶ W) [Etale f.left] :
    (spacesEtaleSite.fiber j f).left = pullback j.left f.left :=
  rfl

/-- The structure morphism of `spacesEtaleSite.fiber j f` is
`pullback.fst j.left f.left ≫ U.hom`. -/
@[simp]
theorem spacesEtaleSite.fiber_hom {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U V W : spacesEtaleSite X} (j : U ⟶ W) (f : V ⟶ W) [Etale f.left] :
    (spacesEtaleSite.fiber j f).hom = pullback.fst j.left f.left ≫ U.hom :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
