/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Property
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Diagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation

/-!
# Algebraic spaces from flat locally finitely presented atlases

Surjective flat locally finitely presented atlases recognize algebraic spaces under
representability or diagonal hypotheses.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An fppf sheaf admitting a morphism from an algebraic space that is representable by
algebraic spaces, surjective, flat, and locally of finite presentation is an algebraic space. -/
@[stacks 04S6]
theorem IsAlgebraicSpace.of_flat_locallyOfFinitePresentation_surjective
    {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X] (a : X ⟶ F)
    (ha : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) a) :
    IsAlgebraicSpace F :=
  sorry

/-- An fppf sheaf admitting a morphism from a scheme that is representable by algebraic
spaces, surjective, flat, and locally of finite presentation is an algebraic space. -/
@[stacks 04S6]
theorem IsAlgebraicSpace.of_scheme_flat_locallyOfFinitePresentation_surjective
    {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F) {U : Over S}
    (a : yoneda.obj U ⟶ F)
    (ha : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) a) :
    IsAlgebraicSpace F :=
  sorry

/-- An fppf sheaf with diagonal representable by algebraic spaces and a surjective, flat,
locally finitely presented morphism from an algebraic space is an algebraic space. -/
@[stacks 04S6]
theorem IsAlgebraicSpace.of_diag_flat_locallyOfFinitePresentation_surjective
    {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (hΔ : representableByAlgebraicSpaces (Limits.diag F))
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X] (a : X ⟶ F)
    (hP : (representableByAlgebraicSpaces.of_diag_isAlgebraicSpace hΔ a).has
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S))) :
    IsAlgebraicSpace F :=
  sorry

/-- An fppf sheaf with diagonal representable by schemes and a surjective, flat, locally
finitely presented morphism from a scheme is an algebraic space. -/
@[stacks 04S6]
theorem IsAlgebraicSpace.of_schemeDiag_flat_locallyOfFinitePresentation_surjective
    {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag F)) {U : Over S}
    (a : yoneda.obj U ⟶ F)
    (ha : (over (@AlgebraicGeometry.Surjective ⊓ @AlgebraicGeometry.Flat ⊓
        @AlgebraicGeometry.LocallyOfFinitePresentation :
          MorphismProperty Scheme.{u})).presheaf a) :
    IsAlgebraicSpace F :=
  sorry

/-- An fppf sheaf admitting a morphism from a scheme that is representable by schemes,
surjective, flat, and locally of finite presentation is an algebraic space. -/
theorem IsAlgebraicSpace.of_scheme_representable_flat_locallyOfFinitePresentation_surjective
    {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F) {U : Over S}
    (a : yoneda.obj U ⟶ F)
    (ha : (over (@AlgebraicGeometry.Surjective ⊓ @AlgebraicGeometry.Flat ⊓
        @AlgebraicGeometry.LocallyOfFinitePresentation :
          MorphismProperty Scheme.{u})).presheaf a) :
    IsAlgebraicSpace F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
