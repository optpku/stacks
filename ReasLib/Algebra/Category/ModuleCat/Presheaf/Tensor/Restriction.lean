/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CommRing
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Restriction
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor products and restriction of scalars for module presheaves

Restriction of scalars is lax monoidal sectionwise.  This file assembles the sectionwise tensor
comparisons into a reusable morphism of module presheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal

noncomputable section

universe u v w

namespace PresheafOfModules.Restriction

variable {C : Type u} [Category.{v} C]
variable {O O' : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- Restriction of scalars along a morphism of commutative-ring presheaves. -/
noncomputable abbrev functor (b : O ⟶ O') :
    PresheafOfModules (ringPresheaf O') ⥤ PresheafOfModules (ringPresheaf O) :=
  PresheafOfModules.restrictScalars (PresheafOfModules.presheafStructureMap b)

variable (b : O ⟶ O')
variable (F G : PresheafOfModules (ringPresheaf O'))

/-- The sectionwise unit comparison for restriction of scalars. -/
noncomputable def unitComparisonApp (X : Cᵒᵖ) :
    (𝟙_ (PresheafOfModules (ringPresheaf O))).obj X ⟶
      ((functor b).obj (𝟙_ (PresheafOfModules (ringPresheaf O')))).obj X :=
  ε (ModuleCat.restrictScalars (b.app X).hom)

/-- The sectionwise unit comparisons commute with restriction in the indexing category. -/
theorem unitComparisonApp_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (𝟙_ (PresheafOfModules (ringPresheaf O))).map f ≫
        (ModuleCat.restrictScalars ((ringPresheaf O).map f).hom).map
          (unitComparisonApp b Y) =
      unitComparisonApp b X ≫
        ((functor b).obj (𝟙_ (PresheafOfModules (ringPresheaf O')))).map f := sorry

/-- The lax unit morphism for restriction of scalars on module presheaves. -/
noncomputable def unitComparison :
    𝟙_ (PresheafOfModules (ringPresheaf O)) ⟶
      (functor b).obj (𝟙_ (PresheafOfModules (ringPresheaf O'))) where
  app X := unitComparisonApp b X
  naturality f := unitComparisonApp_naturality b f

/-- The sectionwise lax-monoidal comparison for restriction of scalars. -/
noncomputable def tensorComparisonApp (X : Cᵒᵖ) :
    (PresheafOfModules.Monoidal.tensorObj
      ((PresheafOfModules.restrictScalars
        (PresheafOfModules.presheafStructureMap b)).obj F)
      ((PresheafOfModules.restrictScalars
        (PresheafOfModules.presheafStructureMap b)).obj G)).obj X ⟶
      ((PresheafOfModules.restrictScalars
        (PresheafOfModules.presheafStructureMap b)).obj
        (PresheafOfModules.Monoidal.tensorObj F G)).obj X :=
  μ (ModuleCat.restrictScalars (b.app X).hom) (F.obj X) (G.obj X)

/-- The sectionwise tensor comparisons for restriction of scalars commute with restriction in
the indexing category. -/
theorem tensorComparisonApp_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (PresheafOfModules.Monoidal.tensorObj
      ((PresheafOfModules.restrictScalars
        (PresheafOfModules.presheafStructureMap b)).obj F)
      ((PresheafOfModules.restrictScalars
        (PresheafOfModules.presheafStructureMap b)).obj G)).map f ≫
        (ModuleCat.restrictScalars ((ringPresheaf O).map f).hom).map
          (tensorComparisonApp b F G Y) =
      tensorComparisonApp b F G X ≫
        ((PresheafOfModules.restrictScalars
          (PresheafOfModules.presheafStructureMap b)).obj
          (PresheafOfModules.Monoidal.tensorObj F G)).map f := sorry

/-- The canonical lax-monoidal comparison from the tensor of two restricted module presheaves
to the restriction of their tensor product. -/
noncomputable def tensorComparison :
    PresheafOfModules.Monoidal.tensorObj
        ((PresheafOfModules.restrictScalars
          (PresheafOfModules.presheafStructureMap b)).obj F)
        ((PresheafOfModules.restrictScalars
          (PresheafOfModules.presheafStructureMap b)).obj G) ⟶
      (PresheafOfModules.restrictScalars
        (PresheafOfModules.presheafStructureMap b)).obj
        (PresheafOfModules.Monoidal.tensorObj F G) where
  app X := tensorComparisonApp b F G X
  naturality f := tensorComparisonApp_naturality b F G f

/-- The tensor comparison for restriction of scalars is natural in both module presheaves. -/
theorem tensorComparison_natural
    {F F' G G' : PresheafOfModules (ringPresheaf O')}
    (f : F ⟶ F') (g : G ⟶ G') :
    ((functor b).map f ⊗ₘ (functor b).map g) ≫
        tensorComparison b F' G' =
      tensorComparison b F G ≫ (functor b).map (f ⊗ₘ g) := sorry

/-- The tensor comparison for restriction of scalars respects associators. -/
theorem tensorComparison_associativity
    (F G H : PresheafOfModules (ringPresheaf O')) :
    (tensorComparison b F G ⊗ₘ 𝟙 ((functor b).obj H)) ≫
        tensorComparison b (F ⊗ G) H ≫ (functor b).map (α_ F G H).hom =
      (α_ ((functor b).obj F) ((functor b).obj G) ((functor b).obj H)).hom ≫
        (𝟙 ((functor b).obj F) ⊗ₘ tensorComparison b G H) ≫
          tensorComparison b F (G ⊗ H) := sorry

/-- The tensor comparison for restriction of scalars respects the left unitor. -/
theorem tensorComparison_left_unitality
    (F : PresheafOfModules (ringPresheaf O')) :
    (λ_ ((functor b).obj F)).hom =
      (unitComparison b ⊗ₘ 𝟙 ((functor b).obj F)) ≫
        tensorComparison b (𝟙_ (PresheafOfModules (ringPresheaf O'))) F ≫
          (functor b).map (λ_ F).hom := sorry

/-- The tensor comparison for restriction of scalars respects the right unitor. -/
theorem tensorComparison_right_unitality
    (F : PresheafOfModules (ringPresheaf O')) :
    (ρ_ ((functor b).obj F)).hom =
      (𝟙 ((functor b).obj F) ⊗ₘ unitComparison b) ≫
        tensorComparison b F (𝟙_ (PresheafOfModules (ringPresheaf O'))) ≫
          (functor b).map (ρ_ F).hom := sorry

/-- Restriction of scalars on module presheaves is canonically lax monoidal. -/
@[stacks 03EL "lax-monoidal restriction of scalars"]
noncomputable instance functorLaxMonoidal : (functor b).LaxMonoidal :=
  Functor.LaxMonoidal.ofTensorHom
    (unitComparison b) (tensorComparison b)
    (tensorComparison_natural b) (tensorComparison_associativity b)
    (tensorComparison_left_unitality b) (tensorComparison_right_unitality b)

end PresheafOfModules.Restriction
