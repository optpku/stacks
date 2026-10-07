module

public import ReasLib.AlgebraicGeometry.Scheme.Germ

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Germ

/-- Scheme germs form a category under composition of neighborhood representatives. -/
noncomputable instance instCategory : Category Germ where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

end AlgebraicGeometry.Scheme.Germ
