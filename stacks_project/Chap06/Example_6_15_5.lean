module

public import ReasLib.CategoryTheory.Functor.Algebraic.Basic
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe w v u

/- `morphism_factors_through_of_range_subset_of_injective` owns the factorization result.
This example keeps only the source-facing `CommSq` bridge, specialized to `ab ≫ bd` and `cd`.
Using `Subobject.Factors` would additionally require deriving `Mono cd` and bundling `cd` as
`Subobject.mk cd`, without improving recovery of the textbook square; the bridge is therefore the
smaller reusable surface for later diagram arguments. -/

section

variable {𝒞 : Type u} [Category.{v} 𝒞] (F : 𝒞 ⥤ Type w) [IsAlgebraicStructure 𝒞 F]
variable {A B C D : 𝒞} (ab : A ⟶ B) (bd : B ⟶ D) (cd : C ⟶ D)

/- Example 6.15.5: if `C ⟶ D` is injective on underlying sets and the image of the composite
`A ⟶ B ⟶ D` is contained in the image of `C ⟶ D`, then there exists a morphism `A ⟶ C` making
the resulting square commute. -/
@[stacks 007Q]
#check exists_commSq_of_composite_range_subset_of_injective F ab bd cd

end
