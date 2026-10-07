module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Determinant.Exact.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom.Glue
import Mathlib.Tactic.CrossRefAttribute

/-!
# Descent of local determinant morphisms

The determinant formula associated to a locally split short complex first glues as a morphism
into the exterior algebra of the middle term.  It then factors through the determinant kernel.
This file keeps every piece of non-Prop descent data explicit: a covering family, an actual
splitting on each member, compatibility of the local formulas, and the kernel equation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v t t'

namespace SheafOfModules.RingedSite.Determinant.Exact

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v})
variable {S : ShortComplex (ringedSiteModuleCategory J O)}

/-- The family of local ambient determinant formulas associated to chosen splittings on a
family of objects. -/
@[stacks 0B38 "family of local ambient determinant morphisms"]
abbrev ambientFamily
    {I : Type t} (X : I → C)
    [∀ i, HasWeakSheafify (J.over (X i)) AddCommGrpCat.{max u v}]
    [∀ i, (J.over (X i)).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (s : ∀ i, (S.map (Localization.restriction O (X i))).Splitting) :
    ∀ i,
      (tensorObj (sheaf S.X₁) (sheaf S.X₃)).over (X i) ⟶
        (ExteriorAlgebra.sheaf O S.X₂).over (X i) :=
  fun i ↦ splitAmbientHom O (X i) (s i)

/-- Local ambient determinant formulas obtained from arbitrary splittings form a compatible
family on every covering family. -/
@[stacks 0B38 "compatibility of the local ambient determinant family"]
theorem ambientFamily_isCompatible
    {I : Type t} (X : I → C)
    [∀ i, HasWeakSheafify (J.over (X i)) AddCommGrpCat.{max u v}]
    [∀ i, (J.over (X i)).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (s : ∀ i, (S.map (Localization.restriction O (X i))).Splitting) :
    (InternalHom.localFamily O X (ambientFamily O X s)).IsCompatible := sorry

/-- A global ambient morphism has the local determinant formula associated to a family of
splittings when its restrictions realize `ambientFamily`. -/
@[stacks 0B38 "global ambient determinant formula"]
def IsAmbientFormula
    {I : Type t} (X : I → C)
    [∀ i, HasWeakSheafify (J.over (X i)) AddCommGrpCat.{max u v}]
    [∀ i, (J.over (X i)).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (s : ∀ i, (S.map (Localization.restriction O (X i))).Splitting)
    (g : tensorObj (sheaf S.X₁) (sheaf S.X₃) ⟶ ExteriorAlgebra.sheaf O S.X₂) : Prop :=
  InternalHom.IsGluing O X (ambientFamily O X s) g

/-- On a covering family, the local ambient determinant formula has a unique global
realization.  The statement is choice-free: it does not manufacture morphism data from the
provisional internal-Hom sheaf proof. -/
@[stacks 0B38 "existence and uniqueness of the ambient determinant morphism"]
theorem existsUnique_ambientHom
    {I : Type t} {X : I → C}
    [∀ i, HasWeakSheafify (J.over (X i)) AddCommGrpCat.{max u v}]
    [∀ i, (J.over (X i)).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : J.CoversTop X)
    (s : ∀ i, (S.map (Localization.restriction O (X i))).Splitting) :
    ∃! g : tensorObj (sheaf S.X₁) (sheaf S.X₃) ⟶ ExteriorAlgebra.sheaf O S.X₂,
      IsAmbientFormula O X s g := sorry

/-- Global ambient determinant morphisms satisfying the local formula on any two splitting
covers agree. -/
@[stacks 0B38 "independence of the ambient determinant formula"]
theorem ambientHom_unique
    {I : Type t} {K : Type t'} {X : I → C} {Y : K → C}
    [∀ i, HasWeakSheafify (J.over (X i)) AddCommGrpCat.{max u v}]
    [∀ i, (J.over (X i)).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [∀ k, HasWeakSheafify (J.over (Y k)) AddCommGrpCat.{max u v}]
    [∀ k, (J.over (Y k)).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : J.CoversTop X) (hY : J.CoversTop Y)
    (s : ∀ i, (S.map (Localization.restriction O (X i))).Splitting)
    (r : ∀ k, (S.map (Localization.restriction O (Y k))).Splitting)
    {g h : tensorObj (sheaf S.X₁) (sheaf S.X₃) ⟶ ExteriorAlgebra.sheaf O S.X₂}
    (hg : IsAmbientFormula O X s g) (hh : IsAmbientFormula O Y r h) :
    g = h := sorry

/-- Every global realization of the local ambient determinant formula is annihilated by the
determinant action of the middle term. -/
@[reassoc, stacks 0B38 "the ambient determinant formula lies in the determinant"]
theorem ambientHom_comp_action
    {I : Type t} {X : I → C}
    [∀ i, HasWeakSheafify (J.over (X i)) AddCommGrpCat.{max u v}]
    [∀ i, (J.over (X i)).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : J.CoversTop X)
    (s : ∀ i, (S.map (Localization.restriction O (X i))).Splitting)
    {g : tensorObj (sheaf S.X₁) (sheaf S.X₃) ⟶ ExteriorAlgebra.sheaf O S.X₂}
    (hg : IsAmbientFormula O X s g) :
    g ≫ action S.X₂ = 0 := sorry

/-- Lift an explicitly supplied ambient determinant morphism through the determinant kernel. -/
@[stacks 0B38 "lifting an ambient determinant morphism"]
noncomputable def liftAmbient
    (g : tensorObj (sheaf S.X₁) (sheaf S.X₃) ⟶ ExteriorAlgebra.sheaf O S.X₂)
    (hdet : g ≫ action S.X₂ = 0) :
    tensorObj (sheaf S.X₁) (sheaf S.X₃) ⟶ sheaf S.X₂ :=
  lift S.X₂ g hdet

/-- The determinant lift recovers its supplied ambient morphism after the determinant
inclusion. -/
@[reassoc, stacks 0B38 "inclusion formula for an ambient determinant lift"]
theorem liftAmbient_ι
    (g : tensorObj (sheaf S.X₁) (sheaf S.X₃) ⟶ ExteriorAlgebra.sheaf O S.X₂)
    (hdet : g ≫ action S.X₂ = 0) :
    liftAmbient O g hdet ≫ ι S.X₂ = g := sorry

/-- A determinant morphism has the prescribed local exact-sequence formula when, after the
determinant inclusion, each restriction is the split ambient formula. -/
@[stacks 0B38 "local formula for an exact-sequence determinant morphism"]
def IsFormula
    {I : Type t} (X : I → C)
    [∀ i, HasWeakSheafify (J.over (X i)) AddCommGrpCat.{max u v}]
    [∀ i, (J.over (X i)).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (s : ∀ i, (S.map (Localization.restriction O (X i))).Splitting)
    (g : tensorObj (sheaf S.X₁) (sheaf S.X₃) ⟶ sheaf S.X₂) : Prop :=
  ∀ i, SheafOfModules.Hom.over g (X i) ≫
      SheafOfModules.Hom.over (ι S.X₂) (X i) = splitAmbientHom O (X i) (s i)

/-- The determinant-valued local formula is equivalent to the ambient local formula after
composing with the determinant inclusion. -/
@[stacks 0B38 "determinant and ambient local formulas"]
theorem isFormula_iff_isAmbientFormula
    {I : Type t} {X : I → C}
    [∀ i, HasWeakSheafify (J.over (X i)) AddCommGrpCat.{max u v}]
    [∀ i, (J.over (X i)).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (s : ∀ i, (S.map (Localization.restriction O (X i))).Splitting)
    (g : tensorObj (sheaf S.X₁) (sheaf S.X₃) ⟶ sheaf S.X₂) :
    IsFormula O X s g ↔ IsAmbientFormula O X s (g ≫ ι S.X₂) := sorry

/-- Lifting an ambient morphism satisfying the local formula produces a determinant morphism
satisfying the corresponding local formula. -/
@[stacks 0B38 "local formula for the ambient determinant lift"]
theorem liftAmbient_isFormula
    {I : Type t} {X : I → C}
    [∀ i, HasWeakSheafify (J.over (X i)) AddCommGrpCat.{max u v}]
    [∀ i, (J.over (X i)).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (s : ∀ i, (S.map (Localization.restriction O (X i))).Splitting)
    {g : tensorObj (sheaf S.X₁) (sheaf S.X₃) ⟶ ExteriorAlgebra.sheaf O S.X₂}
    (hg : IsAmbientFormula O X s g) (hdet : g ≫ action S.X₂ = 0) :
    IsFormula O X s (liftAmbient O g hdet) := sorry

/-- Determinant morphisms satisfying the local formula on any two splitting covers agree. -/
@[stacks 0B38 "uniqueness of the exact-sequence determinant formula"]
theorem formula_unique
    {I : Type t} {K : Type t'} {X : I → C} {Y : K → C}
    [∀ i, HasWeakSheafify (J.over (X i)) AddCommGrpCat.{max u v}]
    [∀ i, (J.over (X i)).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [∀ k, HasWeakSheafify (J.over (Y k)) AddCommGrpCat.{max u v}]
    [∀ k, (J.over (Y k)).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : J.CoversTop X) (hY : J.CoversTop Y)
    (s : ∀ i, (S.map (Localization.restriction O (X i))).Splitting)
    (r : ∀ k, (S.map (Localization.restriction O (Y k))).Splitting)
    {g h : tensorObj (sheaf S.X₁) (sheaf S.X₃) ⟶ sheaf S.X₂}
    (hg : IsFormula O X s g) (hh : IsFormula O Y r h) :
    g = h := sorry

namespace IsAmbientFormula

/-- Lift an explicitly supplied global realization of the ambient local formula to the
determinant.  The kernel equation is derived from the ambient formula, so callers need not supply
it separately. -/
@[stacks 0B38 "determinant morphism from an explicit global ambient formula"]
noncomputable def toDeterminant
    {I : Type t} {X : I → C}
    [∀ i, HasWeakSheafify (J.over (X i)) AddCommGrpCat.{max u v}]
    [∀ i, (J.over (X i)).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : J.CoversTop X)
    {s : ∀ i, (S.map (Localization.restriction O (X i))).Splitting}
    (g : tensorObj (sheaf S.X₁) (sheaf S.X₃) ⟶ ExteriorAlgebra.sheaf O S.X₂)
    (hg : IsAmbientFormula O X s g) :
    tensorObj (sheaf S.X₁) (sheaf S.X₃) ⟶ sheaf S.X₂ :=
  liftAmbient O g (ambientHom_comp_action O hX s hg)

/-- The determinant morphism obtained from an ambient formula recovers the supplied ambient map
after the determinant inclusion. -/
@[reassoc, stacks 0B38 "inclusion formula for the determinant lift of an ambient formula"]
theorem toDeterminant_ι
    {I : Type t} {X : I → C}
    [∀ i, HasWeakSheafify (J.over (X i)) AddCommGrpCat.{max u v}]
    [∀ i, (J.over (X i)).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : J.CoversTop X)
    {s : ∀ i, (S.map (Localization.restriction O (X i))).Splitting}
    (g : tensorObj (sheaf S.X₁) (sheaf S.X₃) ⟶ ExteriorAlgebra.sheaf O S.X₂)
    (hg : IsAmbientFormula O X s g) :
    toDeterminant O hX g hg ≫ ι S.X₂ = g := sorry

/-- The determinant lift of an ambient formula satisfies the corresponding determinant-valued
local formula. -/
@[stacks 0B38 "local formula for the determinant lift of an ambient formula"]
theorem toDeterminant_isFormula
    {I : Type t} {X : I → C}
    [∀ i, HasWeakSheafify (J.over (X i)) AddCommGrpCat.{max u v}]
    [∀ i, (J.over (X i)).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : J.CoversTop X)
    {s : ∀ i, (S.map (Localization.restriction O (X i))).Splitting}
    (g : tensorObj (sheaf S.X₁) (sheaf S.X₃) ⟶ ExteriorAlgebra.sheaf O S.X₂)
    (hg : IsAmbientFormula O X s g) :
    IsFormula O X s (toDeterminant O hX g hg) := sorry

/-- The determinant lift of an ambient formula is the unique determinant morphism realizing the
same local formula. -/
@[stacks 0B38 "uniqueness of the determinant lift of an ambient formula"]
theorem toDeterminant_eq
    {I : Type t} {X : I → C}
    [∀ i, HasWeakSheafify (J.over (X i)) AddCommGrpCat.{max u v}]
    [∀ i, (J.over (X i)).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : J.CoversTop X)
    {s : ∀ i, (S.map (Localization.restriction O (X i))).Splitting}
    (g : tensorObj (sheaf S.X₁) (sheaf S.X₃) ⟶ ExteriorAlgebra.sheaf O S.X₂)
    (hg : IsAmbientFormula O X s g)
    {f : tensorObj (sheaf S.X₁) (sheaf S.X₃) ⟶ sheaf S.X₂}
    (hf : IsFormula O X s f) :
    toDeterminant O hX g hg = f := sorry

end IsAmbientFormula

/-- On a splitting cover, there is a unique determinant morphism satisfying the local split
formula.  This is the choice-free canonical comparison API. -/
@[stacks 0B38 "existence and uniqueness of the exact-sequence determinant morphism"]
theorem existsUnique_formula
    {I : Type t} {X : I → C}
    [∀ i, HasWeakSheafify (J.over (X i)) AddCommGrpCat.{max u v}]
    [∀ i, (J.over (X i)).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : J.CoversTop X)
    (s : ∀ i, (S.map (Localization.restriction O (X i))).Splitting) :
    ∃! g : tensorObj (sheaf S.X₁) (sheaf S.X₃) ⟶ sheaf S.X₂,
      IsFormula O X s g := sorry

namespace IsFormula

/-- A determinant morphism satisfying the split formula restricts to an isomorphism on each
member of the splitting family when both endpoint module sheaves are finite locally free. -/
@[stacks 0B38 "local invertibility of the exact-sequence determinant formula"]
theorem isIso_restriction
    {I : Type t} {X : I → C}
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (s : ∀ i, (S.map (Localization.restriction O (X i))).Splitting)
    (g : tensorObj (sheaf S.X₁) (sheaf S.X₃) ⟶ sheaf S.X₂)
    (hg : IsFormula O X s g) (i : I)
    [SheafOfModules.IsFiniteLocallyFree S.X₁]
    [SheafOfModules.IsFiniteLocallyFree S.X₃] :
    IsIso ((Localization.restriction O (X i)).map g) := sorry

end IsFormula

/-- A determinant morphism satisfying the local split formula is invertible when both endpoint
module sheaves are finite locally free. -/
@[stacks 0B38 "the exact-sequence determinant formula is an isomorphism"]
theorem formula_isIso
    {I : Type t} {X : I → C}
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : J.CoversTop X)
    (s : ∀ i, (S.map (Localization.restriction O (X i))).Splitting)
    (g : tensorObj (sheaf S.X₁) (sheaf S.X₃) ⟶ sheaf S.X₂)
    (hg : IsFormula O X s g)
    [SheafOfModules.IsFiniteLocallyFree S.X₁]
    [SheafOfModules.IsFiniteLocallyFree S.X₃] : IsIso g := sorry

/-- On a splitting cover, the local formula uniquely characterizes an invertible determinant
morphism when both endpoint module sheaves are finite locally free. -/
@[stacks 0B38 "unique invertible exact-sequence determinant comparison"]
theorem existsUnique_formula_isIso
    {I : Type t} {X : I → C}
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (hX : J.CoversTop X)
    (s : ∀ i, (S.map (Localization.restriction O (X i))).Splitting)
    [SheafOfModules.IsFiniteLocallyFree S.X₁]
    [SheafOfModules.IsFiniteLocallyFree S.X₃] :
    ∃! g : tensorObj (sheaf S.X₁) (sheaf S.X₃) ⟶ sheaf S.X₂,
      IsFormula O X s g ∧ IsIso g := sorry

-- `ambientFamily`, `IsAmbientFormula`, and `IsFormula` contain only displayed map data.
-- `liftAmbient` receives both its ambient morphism and kernel equation explicitly.
-- `IsAmbientFormula.toDeterminant` still receives the ambient morphism explicitly; the derived
-- kernel equation is only the Prop-valued witness passed to the canonical determinant lift.

end SheafOfModules.RingedSite.Determinant.Exact
