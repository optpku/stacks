/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.SmoothOnPredeformations
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormallySmoothOnObjects.Representable
public import ReasLib.AlgebraicGeometry.GroupoidsOver.MorphismProperty

/-!
# Formal smoothness implies smoothness on predeformation categories

Over a locally Noetherian scheme, formal smoothness on objects, representable
formal smoothness, and smoothness each imply smoothness on predeformations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- A morphism of categories fibred in groupoids over a locally Noetherian scheme
that is formally smooth on objects induces a smooth functor on predeformation
categories at every finite-type field-valued object. -/
instance IsSmoothOnPredeformations.of_formallySmoothOnObjects
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [FormallySmoothOnObjects f] :
    IsSmoothOnPredeformations f :=
  sorry

/-- A formally smooth morphism of categories fibred in groupoids over a locally
Noetherian scheme that is representable by algebraic spaces induces a smooth
functor on predeformation categories at every finite-type field-valued object. -/
theorem IsSmoothOnPredeformations.of_has_formallySmooth
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X Y : GroupoidsOver S}
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f)
    (h : has (@AlgebraicSpace.FormallySmooth S) f) :
    IsSmoothOnPredeformations f :=
  sorry

/-- A smooth morphism of categories fibred in groupoids over a locally Noetherian
scheme induces a smooth functor on predeformation categories at every finite-type
field-valued object. -/
instance IsSmoothOnPredeformations.of_smooth
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [Smooth f] :
    IsSmoothOnPredeformations f :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
