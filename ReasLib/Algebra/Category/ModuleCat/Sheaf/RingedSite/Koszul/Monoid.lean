/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Derivation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Monoid
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Koszul.Multiplication
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Zero
public import ReasLib.Algebra.Homology.ChainComplex.Monoidal.Symmetric
public import ReasLib.Algebra.Homology.HomologicalComplex.Monoidal.Component
public import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.Tactic.CrossRefAttribute

/-!
# Koszul complexes as commutative monoid objects

The exterior unit and wedge product assemble into chain maps for the Koszul differential.  The
resulting object is the canonical commutative monoid in nonnegative chain complexes, where
commutativity uses the Koszul braiding.  This is the structural owner of the Koszul algebra; the
underlying chain complex and the componentwise exterior algebra remain available through
projection lemmas.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open CategoryTheory.MonObj

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.Koszul

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v})

/-- The exterior unit assembled into a morphism from the tensor-unit chain complex. -/
@[stacks 062K "unit chain map of the Koszul complex"]
noncomputable def oneHom {F : ringedSiteModuleCategory J O}
    (phi : F ⟶ unitModule J O) :
    𝟙_ (ChainComplex (ringedSiteModuleCategory J O) ℕ) ⟶ complex O phi where
  f n :=
    (HomologicalComplex.tensorUnitIso
        (ringedSiteModuleCategory J O) (down ℕ)).inv n ≫
      ExteriorPower.oneHom O F n
  comm' := sorry

/-- Exterior multiplication assembled into a multiplication chain map on the Koszul complex. -/
@[stacks 062K "multiplication chain map of the Koszul complex"]
noncomputable def mulHom {F : ringedSiteModuleCategory J O}
    (phi : F ⟶ unitModule J O) :
    HomologicalComplex.tensorObj (complex O phi) (complex O phi) ⟶ complex O phi where
  f n := HomologicalComplex.mapBifunctorDesc
    (K₁ := complex O phi) (K₂ := complex O phi)
    (F := curriedTensor (ringedSiteModuleCategory J O)) (c := down ℕ)
    fun p q h ↦ ExteriorPower.mul O F p q ≫
      eqToHom (congrArg (complex O phi).X h)
  comm' := sorry

/-- The assembled Koszul unit is a left identity. -/
theorem oneHom_mulHom {F : ringedSiteModuleCategory J O}
    (phi : F ⟶ unitModule J O) :
    oneHom O phi ▷ complex O phi ≫ mulHom O phi =
      (λ_ (complex O phi)).hom := sorry

/-- The assembled Koszul unit is a right identity. -/
theorem mulHom_oneHom {F : ringedSiteModuleCategory J O}
    (phi : F ⟶ unitModule J O) :
    complex O phi ◁ oneHom O phi ≫ mulHom O phi =
      (ρ_ (complex O phi)).hom := sorry

/-- The assembled Koszul multiplication is associative. -/
theorem mulHom_assoc {F : ringedSiteModuleCategory J O}
    (phi : F ⟶ unitModule J O) :
    (mulHom O phi ▷ complex O phi) ≫ mulHom O phi =
      (α_ (complex O phi) (complex O phi) (complex O phi)).hom ≫
        (complex O phi ◁ mulHom O phi) ≫ mulHom O phi := sorry

/-- Exterior multiplication is commutative for the Koszul braiding on chain complexes. -/
theorem mulHom_comm {F : ringedSiteModuleCategory J O}
    (phi : F ⟶ unitModule J O) :
    (β_ (complex O phi) (complex O phi)).hom ≫ mulHom O phi =
      mulHom O phi := sorry

/-- The canonical monoid-object structure on the Koszul chain complex. -/
@[stacks 062K "monoid-object structure on the Koszul complex", implicit_reducible]
noncomputable instance monObj {F : ringedSiteModuleCategory J O}
    (phi : F ⟶ unitModule J O) : MonObj (complex O phi) where
  one := oneHom O phi
  mul := mulHom O phi
  one_mul := oneHom_mulHom O phi
  mul_one := mulHom_oneHom O phi
  mul_assoc := mulHom_assoc O phi

/-- The Koszul chain complex is commutative for the Koszul braiding. -/
@[stacks 062K "commutativity of the Koszul complex"]
noncomputable instance isCommMonObj {F : ringedSiteModuleCategory J O}
    (phi : F ⟶ unitModule J O) : IsCommMonObj (complex O phi) where
  mul_comm := mulHom_comm O phi

/-- The Koszul complex bundled as a commutative monoid object in nonnegative chain complexes
with the Koszul symmetry. -/
@[stacks 062K "Koszul complex as a commutative differential graded algebra", implicit_reducible]
noncomputable def commMon {F : ringedSiteModuleCategory J O}
    (phi : F ⟶ unitModule J O) :
    CommMon (ChainComplex (ringedSiteModuleCategory J O) ℕ) where
  X := complex O phi
  mon := monObj O phi
  comm := isCommMonObj O phi

/-- The underlying chain complex of the bundled Koszul algebra is the Koszul complex. -/
@[simp]
theorem commMon_X {F : ringedSiteModuleCategory J O}
    (phi : F ⟶ unitModule J O) :
    (commMon O phi).X = complex O phi := sorry

/-- The unit of the bundled Koszul algebra is the assembled exterior unit. -/
@[simp]
theorem commMon_one {F : ringedSiteModuleCategory J O}
    (phi : F ⟶ unitModule J O) :
    η[(commMon O phi).X] = oneHom O phi := sorry

/-- The multiplication of the bundled Koszul algebra is the assembled exterior product. -/
@[simp]
theorem commMon_mul {F : ringedSiteModuleCategory J O}
    (phi : F ⟶ unitModule J O) :
    μ[(commMon O phi).X] = mulHom O phi := sorry

/-- The degree-zero component of the bundled Koszul unit is the exterior unit. -/
@[simp, stacks 062K "degree-zero component of the bundled Koszul unit"]
theorem commMon_one_component {F : ringedSiteModuleCategory J O}
    (phi : F ⟶ unitModule J O) :
    HomologicalComplex.Monoidal.unitHomComponent (commMon O phi).mon.one =
      ExteriorPower.gradedOne O F := sorry

/-- The `(n,m)`-component of bundled Koszul multiplication is exterior multiplication. -/
@[simp, stacks 062K "components of bundled Koszul multiplication"]
theorem commMon_mul_component {F : ringedSiteModuleCategory J O}
    (phi : F ⟶ unitModule J O) (n m : ℕ) :
    HomologicalComplex.Monoidal.tensorHomComponent (commMon O phi).mon.mul n m =
      ExteriorPower.mul O F n m := sorry

/-- The degree-zero component of the Koszul unit is the exterior unit. -/
@[simp]
theorem oneHom_component {F : ringedSiteModuleCategory J O}
    (phi : F ⟶ unitModule J O) :
    HomologicalComplex.Monoidal.unitHomComponent (oneHom O phi) =
      ExteriorPower.gradedOne O F := sorry

/-- The `(n,m)`-component of Koszul multiplication is exterior multiplication. -/
@[simp]
theorem mulHom_component {F : ringedSiteModuleCategory J O}
    (phi : F ⟶ unitModule J O) (n m : ℕ) :
    HomologicalComplex.Monoidal.tensorHomComponent (mulHom O phi) n m =
      ExteriorPower.mul O F n m := sorry

/-- On degree one, the Koszul differential is the original map to the structure module. -/
@[stacks 062K "degree-one Koszul differential"]
theorem differential_degreeOne {F : ringedSiteModuleCategory J O}
    (phi : F ⟶ unitModule J O) :
    ExteriorPower.degreeOne O F ≫ differential O phi 0 ≫
      ExteriorPower.degreeZero O F = phi := sorry

/-- The Koszul predifferential is a categorical graded derivation of the exterior algebra. -/
@[stacks 062K "Koszul differential is a graded derivation"]
theorem differential_isDerivation {F : ringedSiteModuleCategory J O}
    (phi : F ⟶ unitModule J O) :
    GradedObject.Monoidal.IsDerivation (ExteriorPower.sheaf O F)
      (ExteriorPower.mul O F) (differential O phi) := sorry

/-- The Koszul differential is the unique exterior derivation with degree-one restriction `phi`. -/
@[stacks 062K "characterization of the Koszul differential"]
theorem differential_unique {F : ringedSiteModuleCategory J O}
    (phi : F ⟶ unitModule J O)
    {d : GradedObject.Predifferential (ExteriorPower.sheaf O F)}
    (hd : GradedObject.Monoidal.IsDerivation (ExteriorPower.sheaf O F)
      (ExteriorPower.mul O F) d)
    (h₁ : ExteriorPower.degreeOne O F ≫ d 0 ≫ ExteriorPower.degreeZero O F = phi) :
    d = differential O phi := sorry

end SheafOfModules.RingedSite.Koszul
