/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

-- Import decisions:
-- * The co-Grothendieck infrastructure is public because the labeled instance exposes its
--   canonical projection and fibred-in-groupoids property.
-- * `StacksCheckRecall` supplies only the source-label attribute and remains a plain import.
public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Presheaf
import StacksCheckRecall

@[expose] public section

universe w v₁ v₂ u

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

variable {𝒞 : Type u} [Category.{v₁} 𝒞]
variable (F : 𝒞ᵒᵖ ⥤ Grpd.{v₂, w})

/- Example 4.37.1 (Stacks 0049): the canonical projection associated to a presheaf of groupoids
is fibred in groupoids. This is the strict-presheaf specialization of
`CoGrothendieck.forgetInGroupoids`.
The result is registered as an instance in the neutral co-Grothendieck module. -/
@[stacks 0049]
#check (groupoidPresheafProjection.inGroupoids F :
  Functor.IsFibered.InGroupoids (groupoidPresheafProjection F))

end CategoryTheory.Pseudofunctor.CoGrothendieck
