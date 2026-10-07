module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Representable

/-- A transformation of presheaves on schemes over a base is representably étale if it is
representable and all its scheme base changes are étale. -/
def Etale {S : Scheme.{u}} : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u) :=
  (MorphismProperty.over (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u})).presheaf

/-- A transformation of presheaves on schemes over a base is a representable open immersion
if it is representable and all its scheme base changes are open immersions. -/
def IsOpenImmersion {S : Scheme.{u}} : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u) :=
  (MorphismProperty.over
    (@AlgebraicGeometry.IsOpenImmersion : MorphismProperty Scheme.{u})).presheaf

/-- A transformation of presheaves on schemes over a base is representably quasi-compact
if it is representable and all its scheme base changes are quasi-compact. -/
def QuasiCompact {S : Scheme.{u}} : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u) :=
  (MorphismProperty.over (@AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u})).presheaf

/-- Every representable open immersion of presheaves is representably étale. -/
theorem isOpenImmersion_etale {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    (ι : F ⟶ G) (h_open : IsOpenImmersion ι) : Etale ι := sorry

end AlgebraicGeometry.AlgebraicSpace.Representable
