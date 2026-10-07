module

public import ReasLib.CategoryTheory.ObjectProperty.Orthogonal.Localization

/-!
# Canonical Comparisons Between Orthogonal Models

For a triangulated object property `P`, two right-orthogonal models related to one source by
morphisms in `P.trW` are canonically isomorphic.  The dual statement compares left-orthogonal
models over one target.  This file is the triangulated bridge to the general local/colocal
comparison API.
-/

@[expose] public section

universe v u

namespace CategoryTheory.ObjectProperty

open Limits Pretriangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {P : ObjectProperty C} [P.IsTriangulated]

namespace rightOrthogonal

namespace comparisonIso

/-- The forward and reverse canonical extensions between right-orthogonal models compose to
the identity on the first model. -/
theorem hom_inv_id {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
    (hf : P.trW f) (hg : P.trW g)
    (hY : P.rightOrthogonal Y) (hZ : P.rightOrthogonal Z) :
    extension hf hZ g ≫ extension hg hY f = 𝟙 Y := sorry

/-- The reverse and forward canonical extensions between right-orthogonal models compose to
the identity on the second model. -/
theorem inv_hom_id {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
    (hf : P.trW f) (hg : P.trW g)
    (hY : P.rightOrthogonal Y) (hZ : P.rightOrthogonal Z) :
    extension hg hY f ≫ extension hf hZ g = 𝟙 Z := sorry

end comparisonIso

/-- The canonical isomorphism between two right-orthogonal `P.trW`-models of one object. -/
@[stacks 0A8E "canonical comparison of right-orthogonal models"]
noncomputable def comparisonIso {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
    (hf : P.trW f) (hg : P.trW g)
    (hY : P.rightOrthogonal Y) (hZ : P.rightOrthogonal Z) : Y ≅ Z where
  hom := extension hf hZ g
  inv := extension hg hY f
  hom_inv_id := comparisonIso.hom_inv_id hf hg hY hZ
  inv_hom_id := comparisonIso.inv_hom_id hf hg hY hZ

namespace comparisonIso

/-- The forward comparison of right-orthogonal models is the canonical extension. -/
@[simp]
theorem hom {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
    (hf : P.trW f) (hg : P.trW g)
    (hY : P.rightOrthogonal Y) (hZ : P.rightOrthogonal Z) :
    (comparisonIso hf hg hY hZ).hom = extension hf hZ g := sorry

/-- The inverse comparison of right-orthogonal models is the reverse canonical extension. -/
@[simp]
theorem inv {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
    (hf : P.trW f) (hg : P.trW g)
    (hY : P.rightOrthogonal Y) (hZ : P.rightOrthogonal Z) :
    (comparisonIso hf hg hY hZ).inv = extension hg hY f := sorry

/-- The forward right-orthogonal comparison restricts to the second model map. -/
@[reassoc]
theorem hom_fac {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
    (hf : P.trW f) (hg : P.trW g)
    (hY : P.rightOrthogonal Y) (hZ : P.rightOrthogonal Z) :
    f ≫ (comparisonIso hf hg hY hZ).hom = g := sorry

/-- The inverse right-orthogonal comparison restricts to the first model map. -/
@[reassoc]
theorem inv_fac {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
    (hf : P.trW f) (hg : P.trW g)
    (hY : P.rightOrthogonal Y) (hZ : P.rightOrthogonal Z) :
    g ≫ (comparisonIso hf hg hY hZ).inv = f := sorry

/-- The canonical comparison of a right-orthogonal model with itself is the identity. -/
@[simp]
theorem refl {X Y : C} {f : X ⟶ Y} (hf : P.trW f) (hY : P.rightOrthogonal Y) :
    comparisonIso hf hf hY hY = Iso.refl Y := sorry

/-- Reversing the two right-orthogonal models reverses their canonical comparison. -/
@[simp]
theorem symm {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
    (hf : P.trW f) (hg : P.trW g)
    (hY : P.rightOrthogonal Y) (hZ : P.rightOrthogonal Z) :
    (comparisonIso hf hg hY hZ).symm = comparisonIso hg hf hZ hY := sorry

/-- Canonical comparisons of right-orthogonal models compose transitively. -/
@[simp]
theorem trans {X Y Z T : C} {f : X ⟶ Y} {g : X ⟶ Z} {h : X ⟶ T}
    (hf : P.trW f) (hg : P.trW g) (hh : P.trW h)
    (hY : P.rightOrthogonal Y) (hZ : P.rightOrthogonal Z)
    (hT : P.rightOrthogonal T) :
    (comparisonIso hf hg hY hZ).trans (comparisonIso hg hh hZ hT) =
      comparisonIso hf hh hY hT := sorry

end comparisonIso

end rightOrthogonal

namespace leftOrthogonal

namespace comparisonIso

/-- The forward and reverse canonical lifts between left-orthogonal models compose to the
identity on the first model. -/
theorem hom_inv_id {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hf : P.trW f) (hg : P.trW g)
    (hX : P.leftOrthogonal X) (hY : P.leftOrthogonal Y) :
    lift hg hX f ≫ lift hf hY g = 𝟙 X := sorry

/-- The reverse and forward canonical lifts between left-orthogonal models compose to the
identity on the second model. -/
theorem inv_hom_id {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hf : P.trW f) (hg : P.trW g)
    (hX : P.leftOrthogonal X) (hY : P.leftOrthogonal Y) :
    lift hf hY g ≫ lift hg hX f = 𝟙 Y := sorry

end comparisonIso

/-- The canonical isomorphism between two left-orthogonal `P.trW`-models of one object. -/
@[stacks 0A8E "canonical comparison of left-orthogonal models"]
noncomputable def comparisonIso {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hf : P.trW f) (hg : P.trW g)
    (hX : P.leftOrthogonal X) (hY : P.leftOrthogonal Y) : X ≅ Y where
  hom := lift hg hX f
  inv := lift hf hY g
  hom_inv_id := comparisonIso.hom_inv_id hf hg hX hY
  inv_hom_id := comparisonIso.inv_hom_id hf hg hX hY

namespace comparisonIso

/-- The forward comparison of left-orthogonal models is the canonical lift. -/
@[simp]
theorem hom {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hf : P.trW f) (hg : P.trW g)
    (hX : P.leftOrthogonal X) (hY : P.leftOrthogonal Y) :
    (comparisonIso hf hg hX hY).hom = lift hg hX f := sorry

/-- The inverse comparison of left-orthogonal models is the reverse canonical lift. -/
@[simp]
theorem inv {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hf : P.trW f) (hg : P.trW g)
    (hX : P.leftOrthogonal X) (hY : P.leftOrthogonal Y) :
    (comparisonIso hf hg hX hY).inv = lift hf hY g := sorry

/-- The forward left-orthogonal comparison composes to the first model map. -/
@[reassoc]
theorem hom_fac {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hf : P.trW f) (hg : P.trW g)
    (hX : P.leftOrthogonal X) (hY : P.leftOrthogonal Y) :
    (comparisonIso hf hg hX hY).hom ≫ g = f := sorry

/-- The inverse left-orthogonal comparison composes to the second model map. -/
@[reassoc]
theorem inv_fac {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hf : P.trW f) (hg : P.trW g)
    (hX : P.leftOrthogonal X) (hY : P.leftOrthogonal Y) :
    (comparisonIso hf hg hX hY).inv ≫ f = g := sorry

/-- The canonical comparison of a left-orthogonal model with itself is the identity. -/
@[simp]
theorem refl {X Z : C} {f : X ⟶ Z} (hf : P.trW f) (hX : P.leftOrthogonal X) :
    comparisonIso hf hf hX hX = Iso.refl X := sorry

/-- Reversing the two left-orthogonal models reverses their canonical comparison. -/
@[simp]
theorem symm {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hf : P.trW f) (hg : P.trW g)
    (hX : P.leftOrthogonal X) (hY : P.leftOrthogonal Y) :
    (comparisonIso hf hg hX hY).symm = comparisonIso hg hf hY hX := sorry

/-- Canonical comparisons of left-orthogonal models compose transitively. -/
@[simp]
theorem trans {X Y T Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {h : T ⟶ Z}
    (hf : P.trW f) (hg : P.trW g) (hh : P.trW h)
    (hX : P.leftOrthogonal X) (hY : P.leftOrthogonal Y)
    (hT : P.leftOrthogonal T) :
    (comparisonIso hf hg hX hY).trans (comparisonIso hg hh hY hT) =
      comparisonIso hf hh hX hT := sorry

end comparisonIso

end leftOrthogonal

end CategoryTheory.ObjectProperty
