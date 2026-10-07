module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Retract
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Localization

@[expose] public section

/-!
# Local lifting from finite-free retracts

This file owns the cover-wise lifting property of finite-free retract module sheaves.  It is
stated on a localized ringed-site presentation so later complex-level lifting arguments can use
the same restriction functors without rebuilding the local module category.
-/

open CategoryTheory
open SheafOfModules.RingedSite.Localization

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FiniteFreeRetract

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {O : Sheaf J CommRingCat.{max u v}}

/-- Lemma 21.44.5 (08FN): a morphism from a finite-free retract lifts locally through an
epimorphism after passing to a covering family. -/
@[stacks 08FN]
theorem exists_cover_lift
    {U : C}
    [HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    {E F G : SheafOfModules.{max u v} (ringSheaf (J.over U) (O.over U))}
    (f : E ⟶ F) (p : G ⟶ F) [Epi p]
    (hE : finiteFreeRetractModuleProperty (ringSheaf (J.over U) (O.over U)) E) :
    ∃ (ι : Type (max u v)) (cover : ι → Over U), (J.over U).CoversTop cover ∧
      ∀ i : ι,
        ∃ l : (restriction (O.over U) (cover i)).obj E ⟶
            (restriction (O.over U) (cover i)).obj G,
          l ≫ (restriction (O.over U) (cover i)).map p =
            (restriction (O.over U) (cover i)).map f := sorry

end SheafOfModules.RingedSite.FiniteFreeRetract
