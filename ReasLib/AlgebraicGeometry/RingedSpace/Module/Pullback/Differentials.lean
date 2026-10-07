module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials.Pullback
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback comparison for relative differentials on ringed spaces

A commutative square of ringed spaces makes the pulled universal differential on the upper-left
structure sheaf into a relative derivation.  Its universal pullback descent is the comparison
morphism on relative differentials.  This specialization keeps the ringed-space notation visible
while reusing the site-generic derivation and adjunction infrastructure.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.Differentials

variable {X X' S S' : RingedSpace.{u}}
variable {f : X' ⟶ X} {g : S' ⟶ S} {h : X ⟶ S} {h' : X' ⟶ S'}

/-- The section map obtained by applying the upper structure-sheaf map and then the universal
differential at the upper-left corner. -/
@[stacks 08RU "section formula"]
noncomputable def comparisonSection
    (f : X' ⟶ X) (h' : X' ⟶ S') {U : (Opens X)ᵒᵖ} (t : X.presheaf.obj U) :
    ((RingedSpace.Hom.pushforward f).obj Ω[h']).val.obj U :=
  (d[h']).d ((RingedSpace.Hom.toRingCatSheafHom f).hom.app U t)

/-- Additivity of the section map underlying the pullback comparison derivation. -/
theorem comparisonSection_add {U : (Opens X)ᵒᵖ} (a b : X.presheaf.obj U) :
    comparisonSection f h' (a + b) =
      comparisonSection f h' a + comparisonSection f h' b := sorry

/-- The Leibniz rule for the section map underlying the pullback comparison derivation. -/
theorem comparisonSection_mul {U : (Opens X)ᵒᵖ} (a b : X.presheaf.obj U) :
    comparisonSection f h' (a * b) =
      a • comparisonSection f h' b + b • comparisonSection f h' a := sorry

/-- Naturality of the section map underlying the pullback comparison derivation. -/
theorem comparisonSection_naturality
    {U V : (Opens X)ᵒᵖ} (rho : U ⟶ V) (t : X.presheaf.obj U) :
    comparisonSection f h' (X.presheaf.map rho t) =
      (((RingedSpace.Hom.pushforward f).obj Ω[h']).val.map rho)
        (comparisonSection f h' t) := sorry

/-- Commutativity of the square makes the pulled differential vanish on the base structure
sheaf. -/
theorem comparisonSection_base
    (sq : CommSq f h' h g) {U : (Opens X)ᵒᵖ}
    (a : ((TopCat.Sheaf.pullback CommRingCat.{u} h.hom.base).obj S.sheaf).obj.obj U) :
    comparisonSection f h'
      ((RingedSpace.Hom.inverseImageStructureSheafHomComm h).hom.app U a) = 0 := sorry

/-- The relative derivation obtained by applying the upper structure-sheaf map and then the
universal differential on the upper-left corner. -/
@[stacks 08RU "comparison derivation"]
noncomputable def comparisonDerivation
    (sq : CommSq f h' h g) :
    RingedSpace.Hom.derivations h
      ((RingedSpace.Hom.pushforward f).obj Ω[h']) where
  d {_} := AddMonoidHom.mk'
    (comparisonSection f h')
    (comparisonSection_add (f := f) (h' := h'))
  d_mul := comparisonSection_mul (f := f) (h' := h')
  d_map := comparisonSection_naturality (f := f) (h' := h')
  d_app := comparisonSection_base sq

/-- Evaluation formula for the derivation underlying the comparison morphism. -/
theorem comparisonDerivation_d
    (sq : CommSq f h' h g) {U : (Opens X)ᵒᵖ} (t : X.presheaf.obj U) :
    (comparisonDerivation sq).d t =
      comparisonSection f h' t := sorry

/-- The adjoint morphism from relative differentials to the pushed-forward target
differentials. -/
@[stacks 08RU "adjoint comparison morphism"]
noncomputable def comparisonAdjoint
    (sq : CommSq f h' h g) :
    Ω[h] ⟶ (RingedSpace.Hom.pushforward f).obj Ω[h'] :=
  RingedSpace.Hom.differentialDesc h (comparisonDerivation sq)

/-- The canonical pullback comparison morphism on relative differentials associated to a
commutative square of ringed spaces. -/
@[stacks 08RU "comparison morphism"]
noncomputable def comparison
    (sq : CommSq f h' h g) :
    (RingedSpace.Hom.pullback f).obj Ω[h] ⟶ Ω[h'] :=
  (comparisonDerivation sq).pullbackDesc

/-- A morphism is the differential comparison when its adjoint carries every universal
differential to the differential of the corresponding pulled section. -/
def IsComparison
    (tau : (RingedSpace.Hom.pullback f).obj Ω[h] ⟶ Ω[h']) : Prop :=
  ∀ {U : (Opens X)ᵒᵖ} (t : X.presheaf.obj U),
    ((RingedSpace.Hom.pullbackPushforwardAdjunction f).homEquiv _ _ tau).val.app U
        ((d[h]).d t) =
      comparisonSection f h' t

/-- The sectionwise comparison property is equivalent to the generic universal pullback descent
property. -/
theorem isComparison_iff_isPullbackDesc
    (sq : CommSq f h' h g)
    (tau : (RingedSpace.Hom.pullback f).obj Ω[h] ⟶ Ω[h']) :
    IsComparison tau ↔
      (comparisonDerivation sq).IsPullbackDesc tau := sorry

/-- The canonical comparison satisfies its sectionwise characterization. -/
theorem comparison_isComparison
    (sq : CommSq f h' h g) :
    IsComparison (comparison sq) := sorry

/-- The adjoint of the comparison carries a universal differential to the differential of the
corresponding pulled section. -/
@[simp]
theorem comparison_d
    (sq : CommSq f h' h g) {U : (Opens X)ᵒᵖ} (t : X.presheaf.obj U) :
    ((RingedSpace.Hom.pullbackPushforwardAdjunction f).homEquiv _ _
        (comparison sq)).val.app U ((d[h]).d t) =
      comparisonSection f h' t := sorry

/-- A morphism satisfying the sectionwise characterization is the canonical comparison. -/
theorem eq_comparison
    (sq : CommSq f h' h g)
    {tau : (RingedSpace.Hom.pullback f).obj Ω[h] ⟶ Ω[h']}
    (h_tau : IsComparison tau) :
    tau = comparison sq := sorry

/-- A commutative square of ringed spaces determines a unique pullback comparison morphism on
relative differentials. -/
@[stacks 08RU]
theorem existsUnique_comparison
    (sq : CommSq f h' h g) :
    ∃! tau : (RingedSpace.Hom.pullback f).obj Ω[h] ⟶ Ω[h'],
      IsComparison tau := sorry

end AlgebraicGeometry.RingedSpace.Hom.Differentials
