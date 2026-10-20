module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Sites.Abelian
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.DegreeOne
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Koszul

/-!
# Augmentation of the étale-trace Koszul complex

The truncated Koszul complex of the trace of a surjective étale morphism has a
canonical augmentation to the constant integer sheaf concentrated in degree zero.
This augmentation is a quasi-isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The module-level degree-zero augmentation of the truncated trace Koszul complex
is the inverse first-exterior-power isomorphism followed by the module trace. -/
noncomputable def traceKoszulToConstantComponentModule {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f] :
    (koszulComplexModules f).X 0 ⟶
      SheafOfModules.unit
        (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u}
          (constantIntegerRingSheaf X)) :=
  (ExteriorPower.degreeOneIso.{u + 1, u} (constantIntegerRingSheaf X)
        (extensionByZeroInteger f)).inv ≫
    traceMapModule f

/-- The degree-zero augmentation of the truncated trace Koszul complex is the
underlying module augmentation followed by the comparison to the constant integers. -/
noncomputable def traceKoszulToConstantComponent {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f] :
    (koszulComplex f).X 0 ⟶
      CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology X) :=
  (SheafOfModules.toSheaf
      (CategoryTheory.Sheaf.ringSheafOfComm.{u + 1, u + 1, u}
        (constantIntegerRingSheaf X))).map
      (traceKoszulToConstantComponentModule f) ≫
    (unitAbelianIso X).hom

/-- The degree-zero augmentation of the truncated trace Koszul complex annihilates
the incoming differential. -/
theorem traceKoszulToConstantComponent_comp_d {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f] :
    (koszulComplex f).d 1 0 ≫ traceKoszulToConstantComponent f = 0 :=
  sorry

/-- The canonical augmentation from the truncated trace Koszul complex to the
constant integer sheaf concentrated in degree zero. -/
noncomputable def traceKoszulToConstant {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f] :
    koszulComplex f ⟶
      (ChainComplex.single₀
        (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})).obj
        (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology X)) :=
  (ChainComplex.toSingle₀Equiv (koszulComplex f)
      (CategoryTheory.constantIntegerSheaf.{u + 1, u, u + 1} (smallEtaleTopology X))).symm
    ⟨traceKoszulToConstantComponent f, traceKoszulToConstantComponent_comp_d f⟩

/-- The degree-zero component of the augmentation chain map is the trace
augmentation of the first exterior power. -/
theorem traceKoszulToConstant_f_zero {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f] :
    (traceKoszulToConstant f).f 0 = traceKoszulToConstantComponent f :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero
    (traceKoszulToConstantComponent f) (traceKoszulToConstantComponent_comp_d f)

/-- The trace of a surjective étale morphism of algebraic spaces is an epimorphism. -/
instance instEpiTraceMap {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Surjective f] : Epi (traceMap f) :=
  sorry

/-- The canonical augmentation of the truncated trace Koszul complex of a
surjective étale morphism is a quasi-isomorphism. -/
instance instQuasiIsoTraceKoszulToConstant {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f] :
    QuasiIso (traceKoszulToConstant f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
