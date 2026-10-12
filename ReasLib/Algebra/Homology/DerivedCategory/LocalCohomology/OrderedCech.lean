/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Ordered
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import Mathlib.Algebra.Homology.Embedding.Extend

@[expose] public section

open CategoryTheory
open ComplexShape

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.LocalCohomology.OrderedCech

variable {A : Type u} [CommRing A]

/-- The integer-indexed ordered Čech complex associated to a finite family in `A`. -/
noncomputable def complex {r : ℕ} (f : Fin r → A) :
    CochainComplex (ModuleCat A) ℤ :=
  (LocalizedModule.Away.Cech.Ordered.extended f (ModuleCat.of A A)).extend
    ComplexShape.embeddingUpNat

/-- The projection from the integer-indexed ordered Čech complex to the regular single complex. -/
noncomputable def projection {r : ℕ} (f : Fin r → A) :
    complex f ⟶ (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of A A) :=
  HomologicalComplex.extendMap
      ((CochainComplex.toSingle₀Equiv
        (LocalizedModule.Away.Cech.Ordered.extended f (ModuleCat.of A A))
        (ModuleCat.of A A)).symm (𝟙 (ModuleCat.of A A))) ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat (ModuleCat.of A A)
      (0 : ℕ) (0 : ℤ) rfl).hom

/-- The ordered Čech complex viewed as an object of the derived category. -/
noncomputable def source {r : ℕ} (f : Fin r → A) : DerivedCategory (ModuleCat A) :=
  (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤ DerivedCategory (ModuleCat A)).obj
    (complex f)

/-- The derived projection from the ordered Čech object to the regular module in degree zero. -/
noncomputable def derivedProjection {r : ℕ} (f : Fin r → A) :
    source f ⟶
      (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤ DerivedCategory (ModuleCat A)).obj
        ((HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℤ) 0).obj
          (ModuleCat.of A A)) :=
  (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤ DerivedCategory (ModuleCat A)).map
    (projection f)

end CategoryTheory.DerivedCategory.LocalCohomology.OrderedCech
