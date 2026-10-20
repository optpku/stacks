module

public import Mathlib.Algebra.Homology.Additive
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Koszul
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.IntegerModules

/-!
# Truncated Koszul complex of the étale trace

The complex has degree-`n` term the exterior power of degree `n + 1` of the
integer-module sheaf obtained by extending the constant integers by zero.
Its differentials are the Koszul differentials of the trace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The degree-`n + 1` exterior power `∧^{n+1} (f_! ℤ̲)` as a sheaf of
`ℤ̲`-modules. -/
noncomputable def koszulTerm {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    [Surjective f] (n : ℕ) :
    ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
      (smallEtaleTopology X) (constantIntegerRingSheaf X) :=
  SheafOfModules.RingedSite.ExteriorPower.sheaf
    (constantIntegerRingSheaf X) (extensionByZeroInteger f) (n + 1)

/-- The Koszul term in degree `n` is the exterior power `∧^{n+1} (f_! ℤ̲)`. -/
theorem koszulTerm_def {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    [Surjective f] (n : ℕ) :
    koszulTerm f n =
      SheafOfModules.RingedSite.ExteriorPower.sheaf
        (constantIntegerRingSheaf X) (extensionByZeroInteger f) (n + 1) :=
  sorry

/-- The Koszul differential `∧^{n+2} (f_! ℤ̲) ⟶ ∧^{n+1} (f_! ℤ̲)` of the trace. -/
noncomputable def koszulDifferential {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    [Surjective f] (n : ℕ) :
    SheafOfModules.RingedSite.ExteriorPower.sheaf
        (constantIntegerRingSheaf X) (extensionByZeroInteger f) (n + 2) ⟶
      SheafOfModules.RingedSite.ExteriorPower.sheaf
        (constantIntegerRingSheaf X) (extensionByZeroInteger f) (n + 1) :=
  SheafOfModules.RingedSite.Koszul.differential
    (constantIntegerRingSheaf X) (traceMapModule f) (n + 1)

/-- Consecutive truncated Koszul differentials compose to zero. -/
theorem koszulDifferential_sq {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    [Surjective f] (n : ℕ) :
    koszulDifferential f (n + 1) ≫ koszulDifferential f n = 0 :=
  sorry

/-- The truncated Koszul complex of `Tr_f` as a chain complex of `ℤ̲`-modules, with
degree-`n` term `∧^{n+1} (f_! ℤ̲)`. -/
noncomputable def koszulComplexModules {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Surjective f] :
    ChainComplex
      (ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
        (smallEtaleTopology X) (constantIntegerRingSheaf X)) ℕ :=
  ChainComplex.of
    (fun n ↦ SheafOfModules.RingedSite.ExteriorPower.sheaf
      (constantIntegerRingSheaf X) (extensionByZeroInteger f) (n + 1))
    (koszulDifferential f) (koszulDifferential_sq f)

/-- The degree-`n` term of the module-level truncated Koszul complex is
`∧^{n+1} (f_! ℤ̲)`. -/
theorem koszulComplexModules_X {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Surjective f] (n : ℕ) :
    (koszulComplexModules f).X n =
      SheafOfModules.RingedSite.ExteriorPower.sheaf
        (constantIntegerRingSheaf X) (extensionByZeroInteger f) (n + 1) :=
  sorry

/-- The truncated Koszul complex `K^•(f)` as a chain complex of abelian sheaves on
`X_étale`, with `K^n = ∧^{n+1} (f_! ℤ̲)`. -/
noncomputable def koszulComplex {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Surjective f] :
    ChainComplex (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) ℕ :=
  ((SheafOfModules.toSheaf (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf X))).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (koszulComplexModules f)

/-- The degree-`n` term of `K^•(f)` is the underlying abelian sheaf of
`∧^{n+1} (f_! ℤ̲)`. -/
theorem koszulComplex_X {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    [Surjective f] (n : ℕ) :
    (koszulComplex f).X n =
      (SheafOfModules.toSheaf (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf X))).obj (koszulTerm f n) :=
  sorry

/-- The differential `K^{n+1} ⟶ K^n` is the underlying abelian sheaf map of the
Koszul differential of `Tr_f`. -/
theorem koszulComplex_d {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f]
    [Surjective f] (n : ℕ) :
    (koszulComplex f).d (n + 1) n =
      (SheafOfModules.toSheaf (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (constantIntegerRingSheaf X))).map (koszulDifferential f n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
