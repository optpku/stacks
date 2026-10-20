module

public import Mathlib.RingTheory.FiniteLength
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Cohomology
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler
public import ReasLib.CategoryTheory.InverseSystem.Sequential.PrincipalTorsion
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology of principal torsion towers

This leaf records the site-cohomology consequence of a principal torsion presentation.  The
cohomology functors and the inverse-system shift are canonical owners; the chapter only recalls
the resulting theorem.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace CategoryTheory.SequentialInverseSystem.PrincipalTorsion.Cohomology

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {A : Type w} [CommRing A]
variable [HasWeakSheafify J (ModuleCat.{max u v w} A)]
variable [HasSheafify J AddCommGrpCat.{max u v w}]
variable [HasExt (Sheaf J AddCommGrpCat.{max u v w})]
variable [J.HasSheafCompose
  (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w})]

/-- Lemma 20.36.4 (0BLC): finite or finite-length stage-one cohomology forces the positive tail
of a principal torsion cohomology tower to satisfy the Mittag–Leffler condition. -/
@[stacks 0BLC "Mittag-Leffler tail from stage-one finiteness"]
theorem isMittagLeffler_of_stageOneFinite
    (f : A) (F : SequentialInverseSystem (Sheaf J (ModuleCat A))) (p : ℕ)
    (hF : PrincipalTorsion.IsPresented f F)
    (h₁ : IsFiniteLength A
        ((siteModuleCohomologyFunctor (p + 1)).obj (F.obj (op 1))) ∨
      (IsNoetherianRing A ∧
        Module.Finite A
          ((siteModuleCohomologyFunctor (p + 1)).obj (F.obj (op 1))))) :
    ((siteModuleCohomologyModuleTower F p).shift 1).IsMittagLeffler := sorry

end CategoryTheory.SequentialInverseSystem.PrincipalTorsion.Cohomology
