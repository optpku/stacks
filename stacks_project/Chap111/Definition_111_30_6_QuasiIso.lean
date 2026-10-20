module

public import ReasLib.CategoryTheory.Filtration.Complex.QuasiIso

@[expose] public section

open CategoryTheory

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]

/- A filtered cochain-complex morphism is a filtered quasi-isomorphism precisely when every
induced graded-piece map is a quasi-isomorphism. -/
#check (CategoryTheory.FilteredComplex.IsFilteredQuasiIso :
  ∀ {K L : FilteredComplex A}, (K ⟶ L) → Prop)
