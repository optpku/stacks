/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Property
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation

/-!
# Representability of the diagonal by schemes from an fppf algebraic-space atlas

An fppf sheaf on schemes over `S` that admits a map from an algebraic space
which is representable by algebraic spaces, surjective, flat, and locally of
finite presentation has diagonal representable by schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The diagonal of an fppf sheaf admitting a map from an algebraic space which
is representable by algebraic spaces, surjective, flat, and locally of finite
presentation is representable by schemes. -/
theorem relativelyRepresentable_diag {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X] (a : X ⟶ F)
    (ha : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) a) :
    yoneda.relativelyRepresentable (Limits.diag F) :=
  sorry

/-- Every map from a scheme over `S` to an fppf sheaf admitting an algebraic-space
atlas that is representable by algebraic spaces, surjective, flat, and locally of
finite presentation is representable by schemes. -/
theorem relativelyRepresentable_yoneda {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X] (a : X ⟶ F)
    (ha : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) a)
    ⦃T : Over S⦄ (ξ : yoneda.obj T ⟶ F) :
    yoneda.relativelyRepresentable ξ :=
  sorry

/-- Pairwise fibre products of Yoneda sections of an fppf sheaf admitting an
algebraic-space atlas that is representable by algebraic spaces, surjective,
flat, and locally of finite presentation are representable. -/
theorem isRepresentable_pullback {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X] (a : X ⟶ F)
    (ha : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) a)
    ⦃T T' : Over S⦄ (ξ : yoneda.obj T ⟶ F) (ξ' : yoneda.obj T' ⟶ F) :
    (pullback ξ ξ').IsRepresentable :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
