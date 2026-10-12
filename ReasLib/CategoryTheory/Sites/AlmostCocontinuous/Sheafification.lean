/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.AlmostCocontinuous
public import ReasLib.CategoryTheory.Sites.SheafificationComparison
public import ReasLib.CategoryTheory.Sites.SheafTheoreticEmpty.Sections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Almost cocontinuity and sheafification

Almost cocontinuity makes the continuous sheafification comparison invertible for
presheaves that are uniquely inhabited on sheaf-theoretically empty objects.
-/

@[expose] public section

open CategoryTheory Opposite

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.Functor.IsAlmostCocontinuous

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
variable [K.WEqualsLocallyBijective (Type w)]
variable [u.IsContinuous J K] [u.IsAlmostCocontinuous J K]

/-- The continuous sheafification comparison is an isomorphism at a presheaf whose sections are
unique on all sheaf-theoretically empty target objects. -/
@[stacks 04B8]
theorem continuousSheafificationComparison_app_isIso
    (G : Dᵒᵖ ⥤ Type w)
    (hG : ∀ V : D, K.IsSheafTheoreticallyEmpty V → Nonempty (Unique (G.obj (op V)))) :
    IsIso ((u.continuousSheafificationComparison J K).app G) := sorry

/-- The underlying presheaf map of the almost-cocontinuous sheafification comparison is an
isomorphism under the same uniqueness hypothesis. -/
theorem continuousSheafificationComparison_hom_app_isIso
    (G : Dᵒᵖ ⥤ Type w)
    (hG : ∀ V : D, K.IsSheafTheoreticallyEmpty V → Nonempty (Unique (G.obj (op V)))) :
    IsIso (((u.continuousSheafificationComparison J K).app G).hom) := sorry

end CategoryTheory.Functor.IsAlmostCocontinuous

namespace CategoryTheory.Presheaf.HasUniqueSectionsOn

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
variable [u.IsContinuous J K]

/-- The continuous sheafification comparison is invertible for a presheaf with unique sections
on the sheaf-theoretically empty target objects. -/
instance continuousSheafificationComparison_isIso (G : Dᵒᵖ ⥤ Type w)
    [K.WEqualsLocallyBijective (Type w)] [u.IsAlmostCocontinuous J K]
    [HasUniqueSectionsOn G K.IsSheafTheoreticallyEmpty] :
    IsIso ((u.continuousSheafificationComparison J K).app G) := sorry

/-- The underlying presheaf map of the continuous sheafification comparison is invertible under
the same unique-section instance. -/
instance continuousSheafificationComparison_hom_isIso (G : Dᵒᵖ ⥤ Type w)
    [K.WEqualsLocallyBijective (Type w)] [u.IsAlmostCocontinuous J K]
    [HasUniqueSectionsOn G K.IsSheafTheoreticallyEmpty] :
    IsIso (((u.continuousSheafificationComparison J K).app G).hom) := sorry

section

variable (G : Dᵒᵖ ⥤ Type w)
variable [K.WEqualsLocallyBijective (Type w)] [u.IsAlmostCocontinuous J K]
variable [HasUniqueSectionsOn G K.IsSheafTheoreticallyEmpty]

#synth IsIso ((u.continuousSheafificationComparison J K).app G)
#synth IsIso (((u.continuousSheafificationComparison J K).app G).hom)

end

end CategoryTheory.Presheaf.HasUniqueSectionsOn
