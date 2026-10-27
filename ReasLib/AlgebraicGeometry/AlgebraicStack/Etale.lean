/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSmoothLocal.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicStack.EtaleSmoothLocal

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism `f : X ⟶ Y` of algebraic stacks is étale if it is DM and has
the étale-smooth-local-on-source-and-target lift of étale morphisms of
algebraic spaces. -/
class Etale {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop
    extends DM f where
  /-- The étale-smooth-local-on-source-and-target lift of étale holds for `f`. -/
  hasEtaleSmoothLocal :
    hasEtaleSmoothLocalAtSourceAndTarget (@AlgebraicSpace.Etale S) f

/-- A morphism of algebraic stacks is étale if and only if it is DM and has
the étale-smooth-local-on-source-and-target lift of étale. -/
theorem etale_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Etale f ↔
      DM f ∧ hasEtaleSmoothLocalAtSourceAndTarget (@AlgebraicSpace.Etale S) f :=
  sorry

namespace Etale

/-- Representable étaleness implies étaleness as a morphism of algebraic stacks.
Representability supplies the DM condition.

Stacks, Tag 0CIL:
`source/stacks-official-a04446e57ec1/additional-sources-2.md:34707-34739`;
Tag 050E(3): `additional-sources-2.md:27331-27348` in the same source directory. -/
instance of_groupoidsHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.Etale f] : Etale f where
  toDM := DM.of_relativelyRepresentableByAlgebraicSpaces
    (Groupoids.Hom.Etale.representable (f := f))
  hasEtaleSmoothLocal := by
    sorry

/-- For a morphism of algebraic stacks representable by algebraic spaces,
étaleness agrees with representable étaleness. No additional DM hypothesis is
needed, since representability implies DM.

Stacks, Tags 0CIL and 0CIF:
`source/stacks-official-a04446e57ec1/additional-sources-2.md:34707-34739`
and `additional-sources-2.md:34415-34442` in the same source directory. -/
theorem iff_groupoidsHom {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    Etale f ↔ Groupoids.Hom.Etale f := by
  constructor
  · intro h
    apply (Groupoids.Hom.Etale.iff_has f hf).mpr
    sorry
  · intro h
    letI := h
    exact of_groupoidsHom f

/-- The identity morphism of an algebraic stack is étale. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    Etale (𝟙 X) :=
  sorry

/-- An étale morphism of algebraic stacks has the
étale-smooth-local-on-source-and-target lift of étale. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Etale f] :
    hasEtaleSmoothLocalAtSourceAndTarget (@AlgebraicSpace.Etale S) f :=
  sorry

end Etale

end AlgebraicGeometry.AlgebraicStack
