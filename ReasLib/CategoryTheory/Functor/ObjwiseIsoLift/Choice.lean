/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.ObjwiseIsoLift.Equivalence

/-!
# Choice independence for prescribed objectwise lifts

Different prescribed object assignments and comparison isomorphisms produce canonically
isomorphic inverse functors. The construction is the neutral `QuasiInverse.inverseIso`.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.objwiseIsoLift

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable (F : A ⥤ B)

/-- The canonical natural isomorphism between two prescribed objectwise lifts of the same fully
faithful functor. -/
@[stacks 05SG "prescribed objectwise lift choice independence"]
noncomputable def choiceIso
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X))
    (jObj' : B → A) (i' : ∀ X : B, X ≅ F.obj (jObj' X)) :
    objwiseIsoLift F jObj i ≅ objwiseIsoLift F jObj' i' :=
  (quasiInverse F jObj i).inverseIso (quasiInverse F jObj' i')

/-- The canonical choice comparison intertwines the named counits of the two prescribed
objectwise lifts. -/
theorem choiceIso.counit
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X))
    (jObj' : B → A) (i' : ∀ X : B, X ≅ F.obj (jObj' X)) :
    Functor.isoWhiskerRight (choiceIso F jObj i jObj' i') F ≪≫
        (compIso F jObj' i').symm =
      (compIso F jObj i).symm := sorry

/-- The canonical choice comparison intertwines the adjointified units of the associated
equivalences. -/
theorem choiceIso.adjointifiedUnit
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X))
    (jObj' : B → A) (i' : ∀ X : B, X ≅ F.obj (jObj' X)) :
    (equivalence F jObj i).unitIso ≪≫
        Functor.isoWhiskerLeft F (choiceIso F jObj i jObj' i') =
      (equivalence F jObj' i').unitIso := sorry

/-- Comparing a prescribed objectwise lift with itself gives the identity isomorphism. -/
@[simp]
theorem choiceIso.refl
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X)) :
    choiceIso F jObj i jObj i = Iso.refl (objwiseIsoLift F jObj i) := sorry

/-- Reversing a prescribed-lift comparison exchanges its two choices. -/
@[simp]
theorem choiceIso.symm
    [F.Full] [F.Faithful]
    (jObj : B → A) (i : ∀ X : B, X ≅ F.obj (jObj X))
    (jObj' : B → A) (i' : ∀ X : B, X ≅ F.obj (jObj' X)) :
    (choiceIso F jObj i jObj' i').symm =
      choiceIso F jObj' i' jObj i := sorry

/-- Canonical prescribed-lift comparisons compose transitively. -/
theorem choiceIso.trans
    [F.Full] [F.Faithful]
    (jObj₀ : B → A) (i₀ : ∀ X : B, X ≅ F.obj (jObj₀ X))
    (jObj₁ : B → A) (i₁ : ∀ X : B, X ≅ F.obj (jObj₁ X))
    (jObj₂ : B → A) (i₂ : ∀ X : B, X ≅ F.obj (jObj₂ X)) :
    choiceIso F jObj₀ i₀ jObj₁ i₁ ≪≫ choiceIso F jObj₁ i₁ jObj₂ i₂ =
      choiceIso F jObj₀ i₀ jObj₂ i₂ := sorry

/- Axiom audit: `choiceIso` is the canonical inverse-functor isomorphism of two explicit
quasi-inverses; it introduces no object-equality transport. -/

end CategoryTheory.Functor.objwiseIsoLift
