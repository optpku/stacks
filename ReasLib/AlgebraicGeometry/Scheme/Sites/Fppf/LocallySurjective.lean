/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.Scheme

/-- A representable flat, locally finitely presented, surjective morphism of fppf sheaves is locally surjective. -/
theorem isLocallySurjective_of_representable_fppf
    {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G)
    (ha : (over (@Flat ⊓ @LocallyOfFinitePresentation ⊓ @Surjective :
      MorphismProperty Scheme.{u})).presheaf a) :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) a := sorry

end AlgebraicGeometry.Scheme
