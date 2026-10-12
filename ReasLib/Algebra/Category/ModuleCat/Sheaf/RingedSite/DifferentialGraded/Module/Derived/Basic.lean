/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Homotopy.QuasiIso
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived category of differential graded module sheaves

The DG derived category is the Verdier quotient of the intrinsic DG homotopy category by its
acyclic objects. It is not the ordinary derived category of the abelian category of DG modules,
which would model an additional complex direction.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DifferentialGradedCategory
open scoped CategoryTheory.ObjectProperty
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

-- Mathlib keeps this canonical finite-biproduct construction non-global.  The Verdier quotient
-- must use the same pinned choice as the intrinsic homotopy-category triangulation.
attribute [local instance] Abelian.hasFiniteBiproducts

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- The derived category of differential graded `𝒜`-module sheaves. -/
@[stacks 0FT5]
abbrev DerivedCategory (𝒜 : DGA(𝒪)) :=
  ObjectProperty.verdierQuotient (Homotopy.acyclic 𝒜)

namespace DerivedCategory

/-- The canonical localization from the DG homotopy category to the DG derived category. -/
@[stacks 0FT5]
abbrev Qh (𝒜 : DGA(𝒪)) :
    K ℤ Mod(𝒜, d) ⥤ DerivedCategory 𝒜 :=
  ObjectProperty.verdierQuotientFunctor (Homotopy.acyclic 𝒜)

/-- The canonical functor from DG modules to their derived category. -/
def Q (𝒜 : DGA(𝒪)) : Mod(𝒜, d) ⥤ DerivedCategory 𝒜 :=
  toK 𝒜 ⋙ Qh 𝒜

/-- The canonical homotopy-to-derived functor localizes at DG homotopy
quasi-isomorphisms. -/
@[stacks 0FT5]
instance qhIsLocalization (𝒜 : DGA(𝒪)) :
    (Qh 𝒜).IsLocalization (Homotopy.quasiIso 𝒜) := sorry

/-- The canonical module-to-derived functor localizes at DG-module quasi-isomorphisms. -/
instance qIsLocalization (𝒜 : DGA(𝒪)) :
    (Q 𝒜).IsLocalization (Module.quasiIso 𝒜) := sorry

/-- The image of every DG homotopy quasi-isomorphism under `Qh` is invertible. -/
theorem qhMap_isIso (𝒜 : DGA(𝒪)) {X Y : K ℤ Mod(𝒜, d)}
    (f : X ⟶ Y) (hf : Homotopy.quasiIso 𝒜 f) :
    IsIso ((Qh 𝒜).map f) := sorry

/-- The image of every DG-module quasi-isomorphism under `Q` is invertible. -/
theorem qMap_isIso (𝒜 : DGA(𝒪)) {X Y : Mod(𝒜, d)}
    (f : X ⟶ Y) (hf : Module.quasiIso 𝒜 f) :
    IsIso ((Q 𝒜).map f) := sorry

/-- The canonical module-to-derived functor is additive. -/
instance qAdditive (𝒜 : DGA(𝒪)) : (Q 𝒜).Additive := sorry

/-- The canonical module-to-derived functor commutes with integer shifts. -/
noncomputable instance qCommShift (𝒜 : DGA(𝒪)) :
    (Q 𝒜).CommShift ℤ :=
  Functor.CommShift.comp (toK 𝒜) (Qh 𝒜)

/-- On objects, the module-to-derived functor first regards a DG module as an object of its
homotopy category. -/
theorem Q_obj (𝒜 : DGA(𝒪)) (X : Mod(𝒜, d)) :
    (Q 𝒜).obj X = (Qh 𝒜).obj ⟨X⟩ := sorry

/-- On morphisms, the module-to-derived functor maps the represented DG homotopy class. -/
theorem Q_map (𝒜 : DGA(𝒪)) {X Y : Mod(𝒜, d)} (f : X ⟶ Y) :
    (Q 𝒜).map f = (Qh 𝒜).map ((toK 𝒜).map f) := sorry

end DerivedCategory

end


end SheafOfModules.RingedSite.DifferentialGradedModule
