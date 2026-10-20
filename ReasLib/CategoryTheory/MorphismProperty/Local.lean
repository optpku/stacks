module

public import Mathlib.CategoryTheory.ObjectProperty.Local
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Hom Equivalences for Local and Colocal Objects

An object local with respect to a morphism property turns precomposition by every morphism in
that property into a bijection.  This file promotes that bijection to a reusable equivalence and
exposes its canonical extension API.  The dual construction gives lifts into colocal sources.
-/

@[expose] public section

universe v u

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C}

namespace isLocal

/-- Precomposition by a morphism in `W`, with a `W`-local target, as a Hom equivalence. -/
@[simps! apply]
noncomputable def homEquiv {X Y : C} {f : X ⟶ Y} (hf : W f) (Z : C)
    (hZ : W.isLocal Z) : (Y ⟶ Z) ≃ (X ⟶ Z) :=
  Equiv.ofBijective (fun g ↦ f ≫ g) (hZ f hf)

/-- Extend a morphism into a local object across a morphism in `W`. -/
noncomputable def extension {X Y Z : C} {f : X ⟶ Y} (hf : W f)
    (hZ : W.isLocal Z) (g : X ⟶ Z) : Y ⟶ Z :=
  (homEquiv hf Z hZ).symm g

/-- The canonical extension restricts to the original morphism. -/
@[reassoc]
theorem extension_fac {X Y Z : C} {f : X ⟶ Y} (hf : W f)
    (hZ : W.isLocal Z) (g : X ⟶ Z) :
    f ≫ extension hf hZ g = g := sorry

/-- A morphism with the defining restriction property is the canonical extension. -/
theorem extension_unique {X Y Z : C} {f : X ⟶ Y} (hf : W f)
    (hZ : W.isLocal Z) (g : X ⟶ Z) {h : Y ⟶ Z} (hh : f ≫ h = g) :
    h = extension hf hZ g := sorry

/-- The canonical extension is the unique morphism with the prescribed restriction. -/
theorem existsUnique_extension {X Y Z : C} {f : X ⟶ Y} (hf : W f)
    (hZ : W.isLocal Z) (g : X ⟶ Z) :
    ∃! h : Y ⟶ Z, f ≫ h = g := sorry

/-- Canonical extension is natural under postcomposition between local targets. -/
theorem extension_comp {X Y Z Z' : C} {f : X ⟶ Y} (hf : W f)
    (hZ : W.isLocal Z) (hZ' : W.isLocal Z') (g : X ⟶ Z) (k : Z ⟶ Z') :
    extension hf hZ' (g ≫ k) = extension hf hZ g ≫ k := sorry

end isLocal

namespace isColocal

/-- Postcomposition by a morphism in `W`, with a `W`-colocal source, as a Hom equivalence. -/
@[simps! apply]
noncomputable def homEquiv {Y Z : C} {g : Y ⟶ Z} (hg : W g) (X : C)
    (hX : W.isColocal X) : (X ⟶ Y) ≃ (X ⟶ Z) :=
  Equiv.ofBijective (fun f ↦ f ≫ g) (hX g hg)

/-- Lift a morphism from a colocal object through a morphism in `W`. -/
noncomputable def lift {X Y Z : C} {g : Y ⟶ Z} (hg : W g)
    (hX : W.isColocal X) (f : X ⟶ Z) : X ⟶ Y :=
  (homEquiv hg X hX).symm f

/-- The canonical lift composes to the original morphism. -/
@[reassoc]
theorem lift_fac {X Y Z : C} {g : Y ⟶ Z} (hg : W g)
    (hX : W.isColocal X) (f : X ⟶ Z) :
    lift hg hX f ≫ g = f := sorry

/-- A morphism with the defining factorization property is the canonical lift. -/
theorem lift_unique {X Y Z : C} {g : Y ⟶ Z} (hg : W g)
    (hX : W.isColocal X) (f : X ⟶ Z) {h : X ⟶ Y} (hh : h ≫ g = f) :
    h = lift hg hX f := sorry

/-- The canonical lift is the unique morphism with the prescribed composite. -/
theorem existsUnique_lift {X Y Z : C} {g : Y ⟶ Z} (hg : W g)
    (hX : W.isColocal X) (f : X ⟶ Z) :
    ∃! h : X ⟶ Y, h ≫ g = f := sorry

/-- Canonical lifting is natural under precomposition between colocal sources. -/
theorem comp_lift {X' X Y Z : C} {g : Y ⟶ Z} (hg : W g)
    (hX' : W.isColocal X') (hX : W.isColocal X) (k : X' ⟶ X) (f : X ⟶ Z) :
    lift hg hX' (k ≫ f) = k ≫ lift hg hX f := sorry

end isColocal

end CategoryTheory.MorphismProperty


