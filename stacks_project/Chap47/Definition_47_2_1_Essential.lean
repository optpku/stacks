module

public import ReasLib.CategoryTheory.Abelian.Essential

open CategoryTheory

universe u v

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {X Y : 𝒜} (A : CategoryTheory.Subobject X) (f : X ⟶ Y)

#check (CategoryTheory.Subobject.IsEssential A : Prop)
#check (CategoryTheory.IsEssentialEpi f : Prop)
