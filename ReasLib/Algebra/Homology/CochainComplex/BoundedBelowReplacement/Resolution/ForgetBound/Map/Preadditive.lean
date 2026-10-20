module

public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.ForgetBound.Map
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Map.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement.Resolution.Variable.Map.Preadditive

/-!
# Additive Compatibility of Forgetting a Lower Cutoff

Forgetting the strict lower cutoff commutes with the dependent additive operations on
resolution maps. These lemmas expose that compatibility without requiring downstream users to
unfold the bundled maps or their model morphisms.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CochainComplex.StrictlyGE.TermsIn.QuasiIsoTo.Map

variable {A : Type u} [Category.{v} A] [Preadditive A] [CategoryWithHomology A]
  {P : ObjectProperty A} {a : ℤ}
  {K L : CochainComplex A ℤ} {f g : K ⟶ L}
  {R : QuasiIsoTo P a K} {S : QuasiIsoTo P a L}

/-- Forgetting the cutoff preserves the zero resolution map. -/
@[simp]
theorem forgetBound_zero (R : QuasiIsoTo P a K) (S : QuasiIsoTo P a L) :
    (zero R S).forgetBound =
      Plus.TermsIn.QuasiIsoTo.Map.zero R.forgetBound S.forgetBound := sorry

/-- Forgetting the cutoff preserves addition of dependent resolution maps. -/
@[simp]
theorem forgetBound_add (m : Map f R S) (n : Map g R S) :
    (add m n).forgetBound =
      Plus.TermsIn.QuasiIsoTo.Map.add m.forgetBound n.forgetBound := sorry

/-- Forgetting the cutoff preserves negation of a dependent resolution map. -/
@[simp]
theorem forgetBound_neg (m : Map f R S) :
    (neg m).forgetBound = Plus.TermsIn.QuasiIsoTo.Map.neg m.forgetBound := sorry

/-- Forgetting the cutoff preserves subtraction of dependent resolution maps. -/
@[simp]
theorem forgetBound_sub (m : Map f R S) (n : Map g R S) :
    (sub m n).forgetBound =
      Plus.TermsIn.QuasiIsoTo.Map.sub m.forgetBound n.forgetBound := sorry

end CochainComplex.StrictlyGE.TermsIn.QuasiIsoTo.Map

