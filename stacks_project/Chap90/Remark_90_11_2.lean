module

public import ReasLib.CategoryTheory.Linear.Functor
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.FGModuleCat.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v uC vC uD vD

variable (R : Type u) [CommRing R]
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
variable [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
variable (F : C ⥤ D)

/- Remark 90.11.2: R-linearity of a functor can be defined between any categories
enriched over ModuleCat R. The Stacks definition specialized this to
L : FGModuleCat R ⥤ ModuleCat R and L : ModuleCat R ⥤ ModuleCat R, which are
the cases needed so far. -/
@[stacks 06I4]
#check (CategoryTheory.Functor.additive_linear_iff_map_smul_add R F :
  (F.Additive ∧ Functor.Linear R F) ↔
    ∀ (X Y : C) (r : R) (f g : X ⟶ Y),
      F.map (r • f + g) = r • F.map f + F.map g)

variable (L : ModuleCat.{v} R ⥤ ModuleCat.{v} R)

/- Both additivity and scalar compatibility apply to endofunctors of ModuleCat R. -/
#check (L.Additive ∧ Functor.Linear R L : Prop)

variable (Lfg : FGModuleCat.{v} R ⥤ ModuleCat.{v} R)

/- They likewise apply to functors FGModuleCat R ⥤ ModuleCat R. -/
#check (Lfg.Additive ∧ Functor.Linear R Lfg : Prop)
