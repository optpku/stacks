module

public import ReasLib.Algebra.Module.Bimodule.Hom
public import ReasLib.Algebra.Module.Graded.Bimodule.Category

/-!
# Forgetting the Grading on Bimodule Morphisms

This file connects degree-zero morphisms of graded bimodules to the universe-polymorphic concrete
morphisms of their underlying algebra bimodules.  It is kept out of the category owner so that
users of the graded category do not acquire a dependency on the concrete ordinary presentation.
-/

@[expose] public section

noncomputable section

namespace GradedModule.Bimodule.Hom

universe x y w v u

variable {ι : Type x} [DecidableEq ι] [AddCommMonoid ι]
variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]
variable {B : Type w} [Ring B] [Algebra R B]
variable {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜]
variable {𝒝 : ι → Submodule R B} [GradedAlgebra 𝒝]

/-- Forget the grading of a degree-zero graded bimodule morphism. -/
@[stacks 09LN "forgetting a graded bimodule morphism"]
def toOrdinary {M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝} (f : Hom M N) :
    Module.Bimodule.Hom (R := R) (A := A) (B := B) (N := M) (N' := N) :=
  ⟨toLinearMap f, sorry⟩

/-- Forgetting the grading preserves the underlying right-linear map. -/
@[simp]
theorem toOrdinary_toRightLinearMap {M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝} (f : Hom M N) :
    Module.Bimodule.Hom.toRightLinearMap (toOrdinary f) = toLinearMap f := sorry

/-- Forgetting the grading preserves identity bimodule morphisms. -/
@[simp]
theorem toOrdinary_id (M : Bimodule.{x, y, w, v, u} 𝒜 𝒝) :
    toOrdinary (id M) =
      Module.Bimodule.Hom.id (R := R) (A := A) (B := B) (N := M) := sorry

/-- Forgetting the grading preserves composition of bimodule morphisms. -/
@[simp]
theorem toOrdinary_comp {L M N : Bimodule.{x, y, w, v, u} 𝒜 𝒝}
    (g : Hom M N) (f : Hom L M) :
    toOrdinary (comp g f) = Module.Bimodule.Hom.comp (toOrdinary g) (toOrdinary f) := sorry

end GradedModule.Bimodule.Hom
