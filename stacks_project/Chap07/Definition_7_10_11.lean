module

public import Mathlib.CategoryTheory.Sites.LeftExact
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (ℱ : Cᵒᵖ ⥤ Type (max u v))

/- Definition 7.10.11: on a site `C`, the sheaf associated to a set-valued presheaf `ℱ` is
the sheaf `ℱ^# := ℱ^{++}` together with the canonical map `ℱ ⟶ ℱ^#`. This is `J.sheafify ℱ`,
definitionally `J.plusObj (J.plusObj ℱ)`, with canonical map `J.toSheafify ℱ`. -/
@[stacks 00WG] #check (J.sheafify ℱ : Cᵒᵖ ⥤ Type (max u v))

@[stacks 00WG] #check (J.toSheafify ℱ : ℱ ⟶ J.sheafify ℱ)

#check ((presheafToSheaf J (Type (max u v))).obj ℱ : Sheaf J (Type (max u v)))

#check (toSheafify J ℱ : ℱ ⟶ sheafify J ℱ)

#check (plusPlusIsoSheafify J (Type (max u v)) ℱ : J.sheafify ℱ ≅ sheafify J ℱ)
