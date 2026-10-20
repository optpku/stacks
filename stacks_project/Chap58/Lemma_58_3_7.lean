module

public import ReasLib.CategoryTheory.Galois
import StacksCheckRecall

@[expose] public section

universe u v w

namespace CategoryTheory

open Limits
open PreGaloisCategory

/- Lemma 58.3.7 (1): the fiber functor of a Galois category is faithful. -/
@[stacks 0BN0]
#check (CategoryTheory.PreGaloisCategory.galoisCategory_fiberFunctor_faithful :
  ∀ {C : Type u} [Category.{v} C] [GaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) [PreGaloisCategory.FiberFunctor F], F.Faithful)

/- Lemma 58.3.7 (2): for a morphism `f : X ⟶ Y` in a Galois category,
`f` is a monomorphism exactly when `F.map f` is injective. -/
@[stacks 0BN0]
#check (CategoryTheory.PreGaloisCategory.fiberFunctor_mono_iff_injective :
  ∀ {C : Type u} [Category.{v} C] [GaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) [PreGaloisCategory.FiberFunctor F]
    {X Y : C} (f : X ⟶ Y), Mono f ↔ Function.Injective (F.map f))

/- Lemma 58.3.7 (3): for a morphism `f : X ⟶ Y` in a Galois category,
`f` is an epimorphism exactly when `F.map f` is surjective. -/
@[stacks 0BN0]
#check (CategoryTheory.PreGaloisCategory.fiberFunctor_epi_iff_surjective :
  ∀ {C : Type u} [Category.{v} C] [GaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) [PreGaloisCategory.FiberFunctor F]
    {X Y : C} (f : X ⟶ Y), Epi f ↔ Function.Surjective (F.map f))

/- Lemma 58.3.7 (4): an object `A` of a Galois category is initial exactly
when its fiber `F.obj A` is empty. -/
@[stacks 0BN0]
#check (CategoryTheory.PreGaloisCategory.galoisCategory_initial_iff_fiber_empty :
  ∀ {C : Type u} [Category.{v} C] [GaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) [PreGaloisCategory.FiberFunctor F] (A : C),
    Nonempty (IsInitial A) ↔ IsEmpty (F.obj A))

/- Lemma 58.3.7 (5): an object `Z` of a Galois category is final exactly
when its fiber `F.obj Z` is a singleton. -/
@[stacks 0BN0]
#check (CategoryTheory.PreGaloisCategory.fiberFunctor_terminal_iff_singleton :
  ∀ {C : Type u} [Category.{v} C] [GaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) [PreGaloisCategory.FiberFunctor F] (Z : C),
    Nonempty (IsTerminal Z) ↔ ∃ z : F.obj Z, ∀ y : F.obj Z, y = z)

/- Lemma 58.3.7 (6): a morphism between connected objects of a Galois
category is an epimorphism. -/
@[stacks 0BN0]
#check (CategoryTheory.PreGaloisCategory.epi_of_connected_objects :
  ∀ {C : Type u} [Category.{v} C] [GaloisCategory C]
    {X Y : C} [IsConnected X] [IsConnected Y] (f : X ⟶ Y), Epi f)

/- Lemma 58.3.7 (7): if `X` is connected and two morphisms `a b : X ⟶ Y`
agree under `F` at one element of `F.obj X`, then they are equal. -/
@[stacks 0BN0]
#check (CategoryTheory.PreGaloisCategory.fiberFunctor_hom_ext_of_isConnected :
  ∀ {C : Type u} [Category.{v} C] [GaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) [PreGaloisCategory.FiberFunctor F]
    {X Y : C} [IsConnected X] (a b : X ⟶ Y) (x : F.obj X)
    (_ : F.map a x = F.map b x), a = b)

/- Lemma 58.3.7 (8): a morphism between finite coproducts of connected
objects is induced by a function on the indexing types and component morphisms. -/
@[stacks 0BN0]
#check (CategoryTheory.PreGaloisCategory.coproduct_map_of_connected_components :
  ∀ {C : Type u} [Category.{v} C] [GaloisCategory C] (n m : ℕ) (X₀ Y₀ : C)
    (X : Fin n → C) (Y : Fin m → C) (hX : X₀ ≅ ∐ X) (hY : Y₀ ≅ ∐ Y) (f : X₀ ⟶ Y₀)
    [∀ i, IsConnected (X i)] [∀ j, IsConnected (Y j)],
    ∃ (α : Fin n → Fin m) (g : ∀ i, X i ⟶ Y (α i)),
      ∀ i, Sigma.ι X i ≫ hX.inv ≫ f ≫ hY.hom = g i ≫ Sigma.ι Y (α i))

end CategoryTheory

end
