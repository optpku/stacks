module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Adjunctions assembled from indexed families

An indexed family of adjunctions `L i ⊣ R i` assembles into an adjunction whose left
adjoint records all `L i` and whose right adjoint takes the product of all `R i`.  The unit,
counit, and Hom equivalence are exposed coordinatewise for use by constructions such as
Godement resolutions.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

variable {I : Type w}
variable {C : Type u₁} [Category.{v₁} C]
variable {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]
variable (L : ∀ i, C ⥤ D i) (R : ∀ i, D i ⥤ C)
variable (adj : ∀ i, L i ⊣ R i) [HasProductsOfShape I C]

namespace Pi

/-- The component of the unit obtained by lifting the units of all the indexed adjunctions to
their product. -/
noncomputable def unitApp (X : C) :
    X ⟶
      (Functor.pi' L ⋙ (Functor.pi R ⋙ Limits.Pi.functor I)).obj X :=
  Limits.Pi.lift (fun i ↦ (adj i).unit.app X)

/-- Naturality of the product lift defining `unitApp`. -/
theorem unitApp_naturality {X Y : C} (f : X ⟶ Y) :
    (𝟭 C : C ⥤ C).map f ≫ unitApp L R adj Y =
      unitApp L R adj X ≫
        (Functor.pi' L ⋙ (Functor.pi R ⋙ Limits.Pi.functor I)).map f := sorry

/-- The unit assembled from the units of the indexed adjunctions. -/
noncomputable def unit :
    (𝟭 C : C ⥤ C) ⟶ Functor.pi' L ⋙ (Functor.pi R ⋙ Limits.Pi.functor I) where
  app := unitApp L R adj
  naturality := fun _ _ f ↦ unitApp_naturality L R adj f

/-- The assembled unit is the product lift of the component units. -/
@[simp]
theorem unit_app (X : C) :
    (unit L R adj).app X = Limits.Pi.lift (fun i ↦ (adj i).unit.app X) := sorry

/-- Projecting the assembled unit to coordinate `i` recovers the unit of `adj i`. -/
@[reassoc (attr := simp)]
theorem unit_app_π (X : C) (i : I) :
    (unit L R adj).app X ≫
        Limits.Pi.π (fun j ↦ (R j).obj ((L j).obj X)) i =
      (adj i).unit.app X := sorry

/-- The component of the counit.  At coordinate `i`, first project the product of the `R j`,
apply `L i`, and then apply the counit of `adj i`. -/
noncomputable def counitApp (Y : ∀ i, D i) :
    ((Functor.pi R ⋙ Limits.Pi.functor I) ⋙ Functor.pi' L).obj Y ⟶ Y :=
  fun i ↦
    (L i).map (Limits.Pi.π (fun j ↦ (R j).obj (Y j)) i) ≫
      (adj i).counit.app (Y i)

/-- Naturality of the coordinatewise counit maps. -/
theorem counitApp_naturality {Y Z : ∀ i, D i} (f : Y ⟶ Z) :
    (((Functor.pi R ⋙ Limits.Pi.functor I) ⋙ Functor.pi' L).map f) ≫
        counitApp L R adj Z =
      counitApp L R adj Y ≫
        (𝟭 (∀ i, D i) : (∀ i, D i) ⥤ (∀ i, D i)).map f := sorry

/-- The counit assembled from product projections and the coordinate counits. -/
noncomputable def counit :
    (Functor.pi R ⋙ Limits.Pi.functor I) ⋙ Functor.pi' L ⟶
      (𝟭 (∀ i, D i) : (∀ i, D i) ⥤ (∀ i, D i)) where
  app := counitApp L R adj
  naturality := fun _ _ f ↦ counitApp_naturality L R adj f

/-- The `i`-th component of the assembled counit is projection followed by the `i`-th counit. -/
@[simp]
theorem counit_app_apply (Y : ∀ i, D i) (i : I) :
    ((counit L R adj).app Y) i =
      (L i).map (Limits.Pi.π (fun j ↦ (R j).obj (Y j)) i) ≫
        (adj i).counit.app (Y i) := sorry

/-- The left triangle identity for the assembled unit and counit. -/
theorem left_triangle (X : C) :
    (Functor.pi' L).map ((unit L R adj).app X) ≫
        (counit L R adj).app ((Functor.pi' L).obj X) =
      𝟙 ((Functor.pi' L).obj X) := sorry

/-- The right triangle identity for the assembled unit and counit. -/
theorem right_triangle (Y : ∀ i, D i) :
    (unit L R adj).app ((Functor.pi R ⋙ Limits.Pi.functor I).obj Y) ≫
        (Functor.pi R ⋙ Limits.Pi.functor I).map ((counit L R adj).app Y) =
      𝟙 ((Functor.pi R ⋙ Limits.Pi.functor I).obj Y) := sorry

end Pi

/-- The canonical adjunction assembled from a family `L i ⊣ R i`: the left adjoint applies
all `L i`, while the right adjoint applies all `R i` and takes their product. -/
@[stacks 0FKS "adjunction assembled from an indexed family"]
noncomputable def pi :
    Functor.pi' L ⊣ (Functor.pi R ⋙ Limits.Pi.functor I) where
  unit := Pi.unit L R adj
  counit := Pi.counit L R adj
  left_triangle_components := Pi.left_triangle L R adj
  right_triangle_components := Pi.right_triangle L R adj

namespace Pi

/-- The unit of `Adjunction.pi` is the explicitly assembled product unit. -/
@[simp]
theorem adjunction_unit :
    (Adjunction.pi L R adj).unit = unit L R adj := sorry

/-- The counit of `Adjunction.pi` is the explicitly assembled coordinatewise counit. -/
@[simp]
theorem adjunction_counit :
    (Adjunction.pi L R adj).counit = counit L R adj := sorry

/-- The forward Hom equivalence of `Adjunction.pi`, after projection to coordinate `i`, is the
forward Hom equivalence of `adj i`. -/
@[reassoc (attr := simp)]
theorem homEquiv_apply_π (X : C) (Y : ∀ i, D i)
    (f : (Functor.pi' L).obj X ⟶ Y) (i : I) :
    (Adjunction.pi L R adj).homEquiv X Y f ≫
        Limits.Pi.π (fun j ↦ (R j).obj (Y j)) i =
      (adj i).homEquiv X (Y i) (f i) := sorry

/-- The inverse Hom equivalence of `Adjunction.pi` is computed coordinatewise after projecting
from the product. -/
@[simp]
theorem homEquiv_symm_apply_apply (X : C) (Y : ∀ i, D i)
    (f : X ⟶ (Functor.pi R ⋙ Limits.Pi.functor I).obj Y) (i : I) :
    ((Adjunction.pi L R adj).homEquiv X Y).symm f i =
      ((adj i).homEquiv X (Y i)).symm
        (f ≫ Limits.Pi.π (fun j ↦ (R j).obj (Y j)) i) := sorry

end Pi

end CategoryTheory.Adjunction
