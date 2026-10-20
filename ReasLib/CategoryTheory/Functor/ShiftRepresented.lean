module

public import Mathlib.CategoryTheory.Whiskering

/-!
# Shifted represented functors

This leaf isolates the formal operation used whenever a family of functors is identified with a
shift of its degree-zero member and that member is represented by a fixed functor.  The operation
is independent of the particular category, coefficient category, or representing object.
-/

@[expose] public section

open CategoryTheory

universe u₁ v₁ u₂ v₂ uι

namespace CategoryTheory.Functor.ShiftRepresented

variable {D : Type u₁} [Category.{v₁} D]
variable {E : Type u₂} [Category.{v₂} E]
variable {ι : Type uι} [Zero ι]

/-- Compose a shift comparison with a degree-zero representing comparison. -/
noncomputable def iso
    (H : ι → D ⥤ E) (S : ι → D ⥤ D) (R : D ⥤ E)
    (hshift : ∀ n : ι, H n ≅ S n ⋙ H 0)
    (hzero : H 0 ≅ R) (n : ι) :
    H n ≅ S n ⋙ R :=
  hshift n ≪≫ Functor.isoWhiskerLeft (S n) hzero

/-- Evaluate `iso` at an object of the source category. -/
noncomputable def objIso
    (H : ι → D ⥤ E) (S : ι → D ⥤ D) (R : D ⥤ E)
    (hshift : ∀ n : ι, H n ≅ S n ⋙ H 0)
    (hzero : H 0 ≅ R) (X : D) (n : ι) :
    (H n).obj X ≅ (S n ⋙ R).obj X :=
  (iso H S R hshift hzero n).app X

/-- The forward component of `iso` is the shifted comparison followed by the representing map. -/
theorem hom_app
    (H : ι → D ⥤ E) (S : ι → D ⥤ D) (R : D ⥤ E)
    (hshift : ∀ n : ι, H n ≅ S n ⋙ H 0)
    (hzero : H 0 ≅ R) (X : D) (n : ι) :
    (iso H S R hshift hzero n).hom.app X =
      (hshift n).hom.app X ≫ (hzero.hom.app ((S n).obj X)) := sorry

/-- The inverse component of `iso` is the representing inverse followed by the shifted inverse. -/
theorem inv_app
    (H : ι → D ⥤ E) (S : ι → D ⥤ D) (R : D ⥤ E)
    (hshift : ∀ n : ι, H n ≅ S n ⋙ H 0)
    (hzero : H 0 ≅ R) (X : D) (n : ι) :
    (iso H S R hshift hzero n).inv.app X =
      (hzero.inv.app ((S n).obj X)) ≫ (hshift n).inv.app X := sorry

end CategoryTheory.Functor.ShiftRepresented
