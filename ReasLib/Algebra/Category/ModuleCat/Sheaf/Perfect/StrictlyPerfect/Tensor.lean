/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Retract.Tensor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Perfect.StrictlyPerfect
public import ReasLib.Algebra.Homology.CochainComplex.Tensor.BoundedTermsIn

/-!
# Tensor products of strictly perfect complexes

This leaf combines the generic bounded-termwise tensor theorem with the canonical tensor closure
of finite-free retract module sheaves.  The natural owner is a commutative ring sheaf on an
arbitrary site, which simultaneously covers ringed sites and ringed spaces.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace SheafOfModules
namespace CochainComplex

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [J.HasSheafCompose
  (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable {O : Sheaf J CommRingCat.{w}}

/-- Tensor products preserve termwise finite-free retractness for bounded complexes. -/
theorem IsTermwiseFiniteFreeRetract.tensorObj
    {K L : _root_.CochainComplex
      (RingedSite.ringedSiteModuleCategory.{u, v, w, w} J O) ℤ}
    [HomologicalComplex.HasTensor K L]
    (hKbounded : _root_.CochainComplex.bounded
      (RingedSite.ringedSiteModuleCategory.{u, v, w, w} J O) K)
    (hLbounded : _root_.CochainComplex.bounded
      (RingedSite.ringedSiteModuleCategory.{u, v, w, w} J O) L)
    (hK : IsTermwiseFiniteFreeRetract K) (hL : IsTermwiseFiniteFreeRetract L) :
    IsTermwiseFiniteFreeRetract (HomologicalComplex.tensorObj K L) := sorry

/-- Lemma 20.46.3 (09J2): the total tensor product of two strictly perfect complexes is strictly
perfect. -/
@[stacks 09J2]
theorem IsStrictlyPerfect.tensorObj
    {K L : _root_.CochainComplex
      (RingedSite.ringedSiteModuleCategory.{u, v, w, w} J O) ℤ}
    [HomologicalComplex.HasTensor K L]
    (hK : IsStrictlyPerfect K) (hL : IsStrictlyPerfect L) :
    IsStrictlyPerfect (HomologicalComplex.tensorObj K L) := sorry

end CochainComplex
end SheafOfModules
