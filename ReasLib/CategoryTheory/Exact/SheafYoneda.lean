/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import ReasLib.CategoryTheory.Exact.Site

@[expose] public section

/-!
# Sheaf-Valued Yoneda Embedding of an Exact Structure

The additive Yoneda presheaves are sheaves for the admissible-epimorphism topology.  Their lift to
sheaves is fully faithful, identifies admissible pairs with short exact sequences, and has
extension-closed essential image.
-/

open CategoryTheory Limits

universe u v

noncomputable section

namespace CategoryTheory.ExactStructure

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasFiniteProducts A]

/-- Every additive representable is a sheaf for the admissible-epimorphism topology. -/
theorem preadditiveYoneda_isSheaf (E : ExactStructure A) (X : A) :
    Presheaf.IsSheaf E.topology (preadditiveYoneda.obj X) := sorry

/-- The sheaf-valued additive Yoneda functor of an exact structure. -/
@[stacks 05SF "sheaf-valued Yoneda embedding"]
def sheafYoneda (E : ExactStructure A) : A ⥤ Sheaf E.topology AddCommGrpCat.{v} :=
  ObjectProperty.lift _ preadditiveYoneda (fun X ↦ preadditiveYoneda_isSheaf E X)

/-- The sheaf-valued Yoneda functor of an exact structure is full. -/
@[stacks 05SF "full sheaf-valued Yoneda embedding"]
instance sheafYoneda_full (E : ExactStructure A) : Functor.Full E.sheafYoneda := sorry

/-- The sheaf-valued Yoneda functor of an exact structure is faithful. -/
@[stacks 05SF "faithful sheaf-valued Yoneda embedding"]
instance sheafYoneda_faithful (E : ExactStructure A) : Functor.Faithful E.sheafYoneda := sorry

/-- The sheaf-valued Yoneda functor sends admissible kernel-cokernel pairs to short exact
sequences. -/
@[stacks 05SF "admissible pairs map to short exact sequences"]
theorem sheafYoneda_maps_admissible
    (E : ExactStructure A) {S : ShortComplex A} (hS : E.admissible S) :
    (S.map E.sheafYoneda).ShortExact := sorry

/-- The sheaf-valued Yoneda functor reflects admissible exact sequences. -/
@[stacks 05SF "sheaf-valued Yoneda reflects admissibility"]
theorem sheafYoneda_reflects_admissible
    (E : ExactStructure A) {S : ShortComplex A} (hS : (S.map E.sheafYoneda).ShortExact) :
    E.admissible S := sorry

/-- A short complex is admissible exactly when its image under the sheaf-valued Yoneda embedding
is short exact. -/
@[stacks 05SF "admissibility detected by sheaf-valued Yoneda"]
theorem sheafYoneda_shortExact_iff
    (E : ExactStructure A) {S : ShortComplex A} :
    (S.map E.sheafYoneda).ShortExact ↔ E.admissible S := sorry

/-- The essential image of the sheaf-valued Yoneda functor is closed under short exact
extensions. -/
@[stacks 05SF "extension-closed sheaf-valued Yoneda image"]
theorem sheafYoneda_essImage_closedUnderExtensions
    (E : ExactStructure A) {S : ShortComplex (Sheaf E.topology AddCommGrpCat.{v})}
    (hS : S.ShortExact) (h₁ : E.sheafYoneda.essImage S.X₁)
    (h₃ : E.sheafYoneda.essImage S.X₃) :
    E.sheafYoneda.essImage S.X₂ := sorry

end CategoryTheory.ExactStructure
