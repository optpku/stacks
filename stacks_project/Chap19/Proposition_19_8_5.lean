module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Grothendieck
import StacksCheckRecall

@[expose] public section

/-!
# Functorial Injective Embeddings for Presheaves of Modules

The Grothendieck-abelian structure of `PresheafOfModules` and the generic construction of
functorial injective embeddings are both owned by ReasLib.  This file is the source-facing
specialization to the notation `PMod(𝒪)`.
-/

open CategoryTheory

universe u v

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (𝒪 : Cᵒᵖ ⥤ RingCat.{max u v})

/- Proposition 19.8.5: presheaves of modules over a ring-valued presheaf admit functorial
injective embeddings. -/
@[stacks 01DV] #check
  (inferInstance : HasFunctorialInjectives (PMod(𝒪)))

end CategoryTheory
