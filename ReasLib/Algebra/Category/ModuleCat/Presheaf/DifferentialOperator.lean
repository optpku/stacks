module

public import ReasLib.Algebra.Category.ModuleCat.DifferentialOperator
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CommRing
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential operators between module presheaves

Differential operators between module presheaves are defined objectwise using
the bundled `ModuleCat` predicate.  This is the functor-category layer shared by
presheaf constructions and by module sheafification.
-/

@[expose] public section

open CategoryTheory

universe u v w z

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C]
variable {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{w}}
variable (φ : O₁ ⟶ O₂)
variable {F G H : PresheafOfModules.{z} (ringPresheaf O₂)}

/-- A morphism between scalar-restricted module presheaves has
differential-operator order at most `k` when every objectwise bundled module
map has that order. -/
@[stacks 09CR "presheaf differential operators"]
def IsDifferentialOperatorOfOrder
    (D : (restrictScalars (presheafStructureMap φ)).obj F ⟶
      (restrictScalars (presheafStructureMap φ)).obj G)
    (k : ℕ) : Prop :=
  ∀ X : Cᵒᵖ, ModuleCat.IsDifferentialOperatorOfOrder (φ.app X).hom (D.app X) k

namespace IsDifferentialOperatorOfOrder

/-- Evaluate a presheaf differential operator at an object. -/
theorem app
    (D : (restrictScalars (presheafStructureMap φ)).obj F ⟶
      (restrictScalars (presheafStructureMap φ)).obj G)
    {k : ℕ} (hD : IsDifferentialOperatorOfOrder φ D k) (X : Cᵒᵖ) :
    ModuleCat.IsDifferentialOperatorOfOrder (φ.app X).hom (D.app X) k := sorry

/-- The zero morphism of restricted module presheaves has every
differential-operator order bound. -/
theorem zero (k : ℕ) :
    IsDifferentialOperatorOfOrder φ
      (0 : (restrictScalars (presheafStructureMap φ)).obj F ⟶
        (restrictScalars (presheafStructureMap φ)).obj G) k := sorry

/-- The sum of two presheaf differential operators with a common bound has the
same bound. -/
theorem add
    {D E : (restrictScalars (presheafStructureMap φ)).obj F ⟶
      (restrictScalars (presheafStructureMap φ)).obj G}
    {k : ℕ} (hD : IsDifferentialOperatorOfOrder φ D k)
    (hE : IsDifferentialOperatorOfOrder φ E k) :
    IsDifferentialOperatorOfOrder φ (D + E) k := sorry

/-- Negation preserves the presheaf differential-operator order bound. -/
theorem neg
    {D : (restrictScalars (presheafStructureMap φ)).obj F ⟶
      (restrictScalars (presheafStructureMap φ)).obj G}
    {k : ℕ} (hD : IsDifferentialOperatorOfOrder φ D k) :
    IsDifferentialOperatorOfOrder φ (-D) k := sorry

/-- The identity morphism is a presheaf differential operator of order zero. -/
theorem id :
    IsDifferentialOperatorOfOrder φ
      (𝟙 ((restrictScalars (presheafStructureMap φ)).obj F)) 0 := sorry

/-- Composing presheaf differential operators adds their order bounds. -/
@[stacks 09CS "composition of presheaf differential operators"]
theorem comp
    {D : (restrictScalars (presheafStructureMap φ)).obj F ⟶
      (restrictScalars (presheafStructureMap φ)).obj G}
    {E : (restrictScalars (presheafStructureMap φ)).obj G ⟶
      (restrictScalars (presheafStructureMap φ)).obj H}
    {k l : ℕ} (hD : IsDifferentialOperatorOfOrder φ D k)
    (hE : IsDifferentialOperatorOfOrder φ E l) :
    IsDifferentialOperatorOfOrder φ (D ≫ E) (k + l) := sorry

/-- A presheaf differential operator has the successor order bound. -/
theorem le_succ
    {D : (restrictScalars (presheafStructureMap φ)).obj F ⟶
      (restrictScalars (presheafStructureMap φ)).obj G}
    {k : ℕ} (hD : IsDifferentialOperatorOfOrder φ D k) :
    IsDifferentialOperatorOfOrder φ D (k + 1) := sorry

/-- A presheaf differential operator has every larger order bound. -/
theorem mono
    {D : (restrictScalars (presheafStructureMap φ)).obj F ⟶
      (restrictScalars (presheafStructureMap φ)).obj G}
    {k l : ℕ} (hD : IsDifferentialOperatorOfOrder φ D k) (hkl : k ≤ l) :
    IsDifferentialOperatorOfOrder φ D l := sorry

/-- Precomposition with an `O₂`-linear presheaf morphism preserves a differential-operator
order bound. -/
theorem precompose
    {F' : PresheafOfModules.{z} (ringPresheaf O₂)} (g : F' ⟶ F)
    {D : (restrictScalars (presheafStructureMap φ)).obj F ⟶
      (restrictScalars (presheafStructureMap φ)).obj G}
    {k : ℕ} (hD : IsDifferentialOperatorOfOrder φ D k) :
    IsDifferentialOperatorOfOrder φ
      ((restrictScalars (presheafStructureMap φ)).map g ≫ D) k := sorry

/-- Postcomposition with an `O₂`-linear presheaf morphism preserves a differential-operator
order bound. -/
theorem postcompose
    {G' : PresheafOfModules.{z} (ringPresheaf O₂)}
    {D : (restrictScalars (presheafStructureMap φ)).obj F ⟶
      (restrictScalars (presheafStructureMap φ)).obj G}
    {k : ℕ} (hD : IsDifferentialOperatorOfOrder φ D k) (g : G ⟶ G') :
    IsDifferentialOperatorOfOrder φ
      (D ≫ (restrictScalars (presheafStructureMap φ)).map g) k := sorry

end IsDifferentialOperatorOfOrder

end PresheafOfModules
