/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Finite limits of direct images of module sheaves

Direct image along a continuous functor is computed by precomposition together with restriction
of scalars.  It therefore preserves finite limits, and in particular monomorphisms.  Registering
these facts globally prevents restriction-to-slice proofs from rebuilding temporary instances.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w z u' v'

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {F : C ⥤ D} {S : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}}
variable [F.IsContinuous J K]

/-- Direct image of module sheaves along a continuous functor preserves finite limits. -/
noncomputable instance pushforward_preservesFiniteLimits
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R) :
    PreservesFiniteLimits (pushforward.{z} φ) := sorry

/-- Direct image of module sheaves along a continuous functor preserves monomorphisms. -/
noncomputable instance pushforward_preservesMonomorphisms
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R) :
    (pushforward.{z} φ).PreservesMonomorphisms := sorry

end SheafOfModules
