module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Matress

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u

namespace HomologicalComplex₂

variable {k : Type u} [Field k]

/-- The double complex obtained by forgetting the scalar multiplication. -/
def forgetModule (K : HomologicalComplex₂ (ModuleCat.{u} k) (up ℤ) (up ℤ)) :
    HomologicalComplex₂ AddCommGrpCat.{u} (up ℤ) (up ℤ) :=
  (((forget₂ (ModuleCat.{u} k) AddCommGrpCat).mapHomologicalComplex (up ℤ)).mapHomologicalComplex
    (up ℤ)).obj K

/-- A `k`-linear double complex is a matress when its additive image is one. -/
def ModuleMatress (K : HomologicalComplex₂ (ModuleCat.{u} k) (up ℤ) (up ℤ))
    (period : K ≅ K.bidegreeShift 3 (-3)) : Prop :=
  let F :=
    ((forget₂ (ModuleCat.{u} k) AddCommGrpCat).mapHomologicalComplex (up ℤ)).mapHomologicalComplex
      (up ℤ)
  HomologicalComplex₂.Matress (forgetModule K) (F.mapIso period)

/-- The oppositely indexed termwise dual double complex. -/
def dualComplex (K : HomologicalComplex₂ (ModuleCat.{u} k) (up ℤ) (up ℤ)) :
    HomologicalComplex₂ (ModuleCat.{u} k) (up ℤ) (up ℤ) :=
  HomologicalComplex₂.ofGradedObject (up ℤ) (up ℤ)
    (fun ⟨p, q⟩ => ModuleCat.of k (Module.Dual k ((K.X (-q)).X (-p))))
    (fun p p' q =>
      ModuleCat.ofHom (((K.X (-q)).d (-p') (-p)).hom.dualMap))
    (fun p q q' =>
      ModuleCat.ofHom (((K.d (-q') (-q)).f (-p)).hom.dualMap))
    (by intros; sorry) (by intros; sorry) (by intros; sorry) (by intros; sorry)
    (by intros; sorry)

namespace ModuleMatress

/-- The canonical signed period isomorphism on the oppositely indexed dual. -/
def dualPeriodIso (K : HomologicalComplex₂ (ModuleCat.{u} k) (up ℤ) (up ℤ))
    (period : K ≅ K.bidegreeShift 3 (-3)) :
    dualComplex K ≅ (dualComplex K).bidegreeShift 3 (-3) := by
  let raw : dualComplex K ≅ (dualComplex K).bidegreeShift 3 (-3) :=
    { hom := HomologicalComplex₂.homMk
        (fun ⟨p, q⟩ =>
          ModuleCat.ofHom (((period.inv.f (-q)).f (-p)).hom.dualMap) ≫
            eqToHom (by
              change ModuleCat.of k (Module.Dual k ((K.X (-q + 3)).X (-p - 3))) =
                ModuleCat.of k
                  (Module.Dual k ((K.X (-(q + -3))).X (-(p + 3))))
              congr 3 <;> try rfl
              all_goals first | rfl | (congr 2 <;> ring)))
        (by intros; sorry) (by intros; sorry)
      inv := HomologicalComplex₂.homMk
        (fun ⟨p, q⟩ =>
          eqToHom (by
              change ModuleCat.of k
                  (Module.Dual k ((K.X (-(q + -3))).X (-(p + 3)))) =
                ModuleCat.of k (Module.Dual k ((K.X (-q + 3)).X (-p - 3)))
              congr 3 <;> try rfl
              all_goals first | rfl | (congr 2 <;> ring)) ≫
            ModuleCat.ofHom (((period.hom.f (-q)).f (-p)).hom.dualMap))
        (by intros; sorry) (by intros; sorry)
      hom_inv_id := by sorry
      inv_hom_id := by sorry }
  exact (-1 : ℤˣ) • raw

/-- The oppositely indexed finite-dimensional dual of a matress is a matress. -/
theorem dualMatress (K : HomologicalComplex₂ (ModuleCat.{u} k) (up ℤ) (up ℤ))
    (period : K ≅ K.bidegreeShift 3 (-3))
    [∀ p q : ℤ, FiniteDimensional k ((K.X p).X q)]
    (hK : ModuleMatress K period) :
    ModuleMatress (dualComplex K) (dualPeriodIso K period) := sorry

end ModuleMatress

end HomologicalComplex₂

end
