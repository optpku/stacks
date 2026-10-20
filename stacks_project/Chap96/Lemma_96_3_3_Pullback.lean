module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Presheaf.Pullback

/-!
# Presheaf inverse-image isomorphisms

Natural isomorphisms induce contravariant isomorphisms of presheaf inverse images.
-/

@[expose] public section

open CategoryTheory

universe u v u' v' w

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]

#check (CategoryTheory.Functor.presheafInverseImageIso :
  ∀ {F G : C ⥤ D} (e : F ≅ G) (A : Type w) [Category A],
    Functor.presheafInverseImage G A ≅ Functor.presheafInverseImage F A)
