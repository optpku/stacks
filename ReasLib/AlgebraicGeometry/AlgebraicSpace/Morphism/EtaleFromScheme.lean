/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

/-!
# Étale morphisms from schemes to algebraic spaces

Étale morphisms from schemes to an algebraic space are stable under composition
with étale scheme maps, can be cancelled in commuting triangles, and descend
along surjective étale scheme maps.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry MorphismProperty

namespace AlgebraicGeometry.AlgebraicSpace

/-- Étaleness of a morphism from a scheme to an algebraic space is preserved by
postcomposition with an étale morphism of schemes. -/
theorem etale_comp {S : Scheme.{u}} {X : AlgebraicSpace S} {U U' : Over S}
    (f : U ⟶ U') [Etale f.left] (φ' : yoneda.obj U' ⟶ X.functorOfPoints)
    (hφ' : (over (@Etale)).presheaf φ') :
    (over (@Etale)).presheaf (yoneda.map f ≫ φ') := sorry

/-- A morphism between schemes mapping étale to an algebraic space is étale when
the two maps to the algebraic space are étale and the triangle commutes. -/
theorem etale_of_comp {S : Scheme.{u}} {X : AlgebraicSpace S} {U U' : Over S}
    (φ : yoneda.obj U ⟶ X.functorOfPoints) (φ' : yoneda.obj U' ⟶ X.functorOfPoints)
    (f : U ⟶ U') (hφ : (over (@Etale)).presheaf φ)
    (hφ' : (over (@Etale)).presheaf φ') (w : φ = yoneda.map f ≫ φ') :
    Etale f.left := sorry

/-- Étaleness of a morphism from a scheme to an algebraic space descends along
a surjective étale morphism of schemes. -/
theorem etale_of_surjective_etale {S : Scheme.{u}} {X : AlgebraicSpace S} {U U' : Over S}
    (f : U ⟶ U') [Surjective f.left] [Etale f.left]
    (φ' : yoneda.obj U' ⟶ X.functorOfPoints)
    (hφ : (over (@Etale)).presheaf (yoneda.map f ≫ φ')) :
    (over (@Etale)).presheaf φ' := sorry

end AlgebraicGeometry.AlgebraicSpace
