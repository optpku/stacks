module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Étale-local surjectivity of representable morphisms
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.Scheme

/-- A representably étale and surjective morphism of presheaves on schemes over
`S` is locally surjective for the étale topology. -/
theorem isLocallySurjective_of_surjective_etale
    {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {φ : F ⟶ G}
    (h_etale : (over (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u})).presheaf φ)
    (h_surj : (over (@AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u})).presheaf φ) :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ :=
  sorry

end AlgebraicGeometry.Scheme
