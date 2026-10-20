module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Algebra

/-!
# Homomorphisms of graded algebra sheaves

This leaf defines degreewise module-sheaf maps between graded algebra sheaves that
commute with multiplication.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {ι : Type} [AddMonoid ι]

namespace GradedAlgebraSheaf

/-- A non-unital homomorphism of graded algebra sheaves is a degreewise family of
module-sheaf maps commuting with the multiplication maps. -/
structure NonUnitalHom (𝒜 ℬ : GradedAlgebraSheaf 𝒪 ι) where
  /-- The degreewise module-sheaf maps. -/
  hom : ∀ n : ι, 𝒜.obj n ⟶ ℬ.obj n
  /-- The degreewise maps commute with multiplication on local sections. -/
  map_mul :
    ∀ (U : Cᵒᵖ) (n m : ι)
      (a : (𝒜.obj n).val.obj U) (b : (𝒜.obj m).val.obj U),
      (((hom (n + m)).val.app U).hom) (𝒜.mul U n m a b) =
        ℬ.mul U n m ((((hom n).val.app U).hom) a) ((((hom m).val.app U).hom) b)

namespace NonUnitalHom

/-- The identity non-unital homomorphism of a graded algebra sheaf. -/
def id (𝒜 : GradedAlgebraSheaf 𝒪 ι) : NonUnitalHom 𝒜 𝒜 where
  hom := fun n ↦ 𝟙 (𝒜.obj n)
  map_mul := by
    intro U n m a b
    rfl

/-- The degree-`n` component of the identity non-unital homomorphism is the identity. -/
@[simp]
theorem id_hom (𝒜 : GradedAlgebraSheaf 𝒪 ι) (n : ι) :
    (id 𝒜).hom n = 𝟙 (𝒜.obj n) := rfl

end NonUnitalHom

end GradedAlgebraSheaf

end

end SheafOfModules.RingedSite

