/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.DegreeOne
public import stacks_project.Chap69.Definition_69_6_2_Koszul

/-!
# Quasi-isomorphism of the truncated étale-trace Koszul complex

The truncated Koszul complex `K^•(f)` of a surjective étale morphism of algebraic
spaces maps to the constant integer sheaf concentrated in degree zero, and this
chain map is a quasi-isomorphism in `Ab(X_étale)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Coefficient change from rings to abelian groups preserves sheafification on the
small étale topology of an algebraic space. -/
instance smallEtaleTopology_preservesSheafification_ringCat (X : AlgebraicSpace S) :
    (smallEtaleTopology X).PreservesSheafification
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) :=
  sorry

/-- Coefficient change from commutative rings to rings preserves sheafification on the
small étale topology of an algebraic space. -/
instance smallEtaleTopology_preservesSheafification_commRingCat (X : AlgebraicSpace S) :
    (smallEtaleTopology X).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  sorry

/-- The canonical comparison from the underlying abelian sheaf of the unit `ℤ̲`-module
to the constant integer sheaf, obtained by commuting the constant sheaf past
coefficient change. -/
noncomputable def unitAbelianToConstantInteger (X : AlgebraicSpace S) :
    (SheafOfModules.toSheaf (integerRingSheaf X)).obj
        (SheafOfModules.unit (integerRingSheaf X)) ⟶
      constantIntegerSheaf X :=
  (sheafCompose (smallEtaleTopology X)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
      ((constantCommuteCompose (smallEtaleTopology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom.app
        (CommRingCat.of (ULift.{u + 1} ℤ))) ≫
    (constantCommuteCompose (smallEtaleTopology X)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).hom.app
      ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} ℤ)))

/-- The module-level degree-zero component of `K^•(f) ⟶ ℤ̲[0]`, given by
`∧^1 (f_! ℤ̲) ≅ f_! ℤ̲` followed by the module trace. -/
noncomputable def traceKoszulToConstantComponentModule {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f] :
    (koszulComplexModules f).X 0 ⟶ SheafOfModules.unit (integerRingSheaf X) :=
  (ExteriorPower.degreeOneIso.{u + 1, u} (constantIntegerRingSheaf X)
        (extensionByZeroInteger f)).inv ≫
    traceMapModule f

/-- The degree-zero component of `K^•(f) ⟶ ℤ̲[0]`, given by `∧^1 (f_! ℤ̲) ≅ f_! ℤ̲`
followed by the trace. -/
noncomputable def traceKoszulToConstantComponent {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f] :
    (koszulComplex f).X 0 ⟶ constantIntegerSheaf X :=
  (SheafOfModules.toSheaf (integerRingSheaf X)).map
      (traceKoszulToConstantComponentModule f) ≫
    unitAbelianToConstantInteger X

/-- The degree-zero component of the truncated Koszul map kills the incoming
differential `K^1 ⟶ K^0`. -/
theorem traceKoszulToConstantComponent_comp_d {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f] :
    (koszulComplex f).d 1 0 ≫ traceKoszulToConstantComponent f = 0 :=
  sorry

/-- The displayed chain map `K^•(f) ⟶ ℤ̲[0]` in `Ab(X_étale)`, sending
`∧^1 (f_! ℤ̲)` to `ℤ̲` by the trace. -/
noncomputable def traceKoszulToConstant {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f] :
    koszulComplex f ⟶
      (ChainComplex.single₀
        (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})).obj
        (constantIntegerSheaf X) :=
  (ChainComplex.toSingle₀Equiv (koszulComplex f) (constantIntegerSheaf X)).symm
    ⟨traceKoszulToConstantComponent f, traceKoszulToConstantComponent_comp_d f⟩

/-- The degree-zero component of `traceKoszulToConstant` is the truncated Koszul
augmentation. -/
theorem traceKoszulToConstant_f_zero {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f] :
    (traceKoszulToConstant f).f 0 = traceKoszulToConstantComponent f :=
  sorry

/-- For a surjective étale morphism, the trace `Tr_f` is an epimorphism. -/
instance instEpiTraceMap {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Surjective f] : Epi (traceMap f) :=
  sorry

/-- For a surjective étale morphism, `K^•(f) ⟶ ℤ̲[0]` is a quasi-isomorphism. -/
instance instQuasiIsoTraceKoszulToConstant {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f] :
    QuasiIso (traceKoszulToConstant f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
