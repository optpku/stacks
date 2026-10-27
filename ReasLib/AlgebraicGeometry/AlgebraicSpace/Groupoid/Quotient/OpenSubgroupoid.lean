/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.OpenSubgroupoid
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.SmallFunctoriality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Algebraic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale

/-!
# Quotient morphisms of open wide subgroupoids

The canonical inclusion of an open wide subgroupoid induces a representable,
surjective, étale morphism between algebraic quotient stacks when the ambient
source and target maps are flat and locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.OpenSubgroupoid

/-- The induced morphism `[U / P] ⟶ [U / R]` of quotient stacks. -/
def quotientHom {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    (H : OpenSubgroupoid G) : SmallQuotient.quotientStack H.toGroupoid ⟶ SmallQuotient.quotientStack G :=
  Hom.quotientStackHom H.hom

/-- `quotientHom` is `Hom.quotientStackHom` of the wide inclusion. -/
theorem quotientHom_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G) :
    H.quotientHom = Hom.quotientStackHom H.hom := sorry

/-- An open wide subgroupoid of a flat, locally finitely presented groupoid has
an algebraic quotient stack. -/
theorem isAlgebraicStack_quotientStack {S : Scheme.{u}}
    {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G)
    (h_flat : Flat G) (h_lfp : LocallyOfFinitePresentation G) :
    AlgebraicStack (SmallQuotient.quotientStack H.toGroupoid) := sorry

/-- The quotient morphism of an open wide subgroupoid of a flat, locally finitely
presented groupoid is representable by algebraic spaces. -/
theorem relativelyRepresentableByAlgebraicSpaces_quotientHom {S : Scheme.{u}}
    {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G)
    (h_flat : Flat G) (h_lfp : LocallyOfFinitePresentation G) :
    relativelyRepresentableByAlgebraicSpaces H.quotientHom := sorry

/-- The quotient morphism of an open wide subgroupoid of a flat, locally finitely
presented groupoid is surjective. -/
theorem surjective_quotientHom {S : Scheme.{u}}
    {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G)
    (h_flat : Flat G) (h_lfp : LocallyOfFinitePresentation G) :
    Groupoids.Hom.Surjective H.quotientHom := sorry

/-- The quotient morphism of an open wide subgroupoid of a flat, locally finitely
presented groupoid is étale. -/
theorem etale_quotientHom {S : Scheme.{u}}
    {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B} (H : OpenSubgroupoid G)
    (h_flat : Flat G) (h_lfp : LocallyOfFinitePresentation G) :
    Groupoids.Hom.Etale H.quotientHom := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.OpenSubgroupoid
