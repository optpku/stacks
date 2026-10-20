/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Property
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation

/-!
# Precomposition cancellation of representability by algebraic spaces

Representability by algebraic spaces can be tested after precomposition with a
representable, surjective, flat, locally finitely presented map of fppf sheaves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `b : G ⟶ H` of fppf sheaves is representable by algebraic spaces
if its composite with a representable, surjective, flat, locally finitely
presented morphism `a : F ⟶ G` is representable by algebraic spaces. -/
@[stacks 0AMP]
theorem representableByAlgebraicSpaces.of_precomp {S : Scheme.{u}}
    {F G H : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (a : F ⟶ G) (b : G ⟶ H)
    (ha : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) a)
    (hba : representableByAlgebraicSpaces (a ≫ b)) :
    representableByAlgebraicSpaces b :=
  sorry

/-- For fppf sheaves `F`, `G`, and `H`, representability by algebraic spaces of
`a ≫ b` is equivalent to representability of `b` when `a : F ⟶ G` is
representable by algebraic spaces, surjective, flat, and locally of finite
presentation. -/
theorem representableByAlgebraicSpaces.of_precomp_iff {S : Scheme.{u}}
    {F G H : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
    (a : F ⟶ G) (b : G ⟶ H)
    (ha : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Flat S ⊓ @LocallyOfFinitePresentation S :
        MorphismProperty (AlgebraicSpace S)) a) :
    representableByAlgebraicSpaces (a ≫ b) ↔ representableByAlgebraicSpaces b :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
