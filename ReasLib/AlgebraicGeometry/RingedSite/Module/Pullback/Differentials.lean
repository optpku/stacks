module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.CommRing.Pullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback comparison for relative differentials on ringed sites

A commutative square of commutative ringed-site presentations makes the pulled universal
differential on the upper-left structure sheaf into a relative derivation.  The comparison map
is its universal pullback descent.  The construction is independent of chapter files and uses
the generic relative-derivation API.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace RingedSite.Hom.Differentials

variable {CX CX' CY CY' : Type u}
variable [Category.{u} CX] [Category.{u} CX'] [Category.{u} CY] [Category.{u} CY']
variable {JX : GrothendieckTopology CX} {JX' : GrothendieckTopology CX'}
variable {JY : GrothendieckTopology CY} {JY' : GrothendieckTopology CY'}
variable [JX.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JX'.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JY.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JY'.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {OX : Sheaf JX CommRingCat.{u}}
variable {OX' : Sheaf JX' CommRingCat.{u}}
variable {OY : Sheaf JY CommRingCat.{u}}
variable {OY' : Sheaf JY' CommRingCat.{u}}

variable
  (f : RingedSite.Hom
    (RingedSite.ofCommRingSheaf JX' OX') (RingedSite.ofCommRingSheaf JX OX))
  (g : RingedSite.Hom
    (RingedSite.ofCommRingSheaf JY' OY') (RingedSite.ofCommRingSheaf JY OY))
  (h : RingedSite.Hom
    (RingedSite.ofCommRingSheaf JX OX) (RingedSite.ofCommRingSheaf JY OY))
  (h' : RingedSite.Hom
    (RingedSite.ofCommRingSheaf JX' OX') (RingedSite.ofCommRingSheaf JY' OY'))

/-- The raw commutativity relation for a square of ringed-site morphisms.  It avoids forcing the
ambient category instance into data-bearing comparison declarations. -/
def Commutes : Prop :=
  RingedSite.Hom.comp f h = RingedSite.Hom.comp h' g

/-- The raw commutativity relation agrees with `CategoryTheory.CommSq`.  Data constructors use
`Commutes` so that proof axioms in the ambient category instance do not contaminate their
computational audit. -/
theorem commutes_iff_commSq :
    Commutes f g h h' ↔
      @CommSq RingedSite.{u, u} RingedSite.instCategory
        (RingedSite.ofCommRingSheaf JX' OX')
        (RingedSite.ofCommRingSheaf JX OX)
        (RingedSite.ofCommRingSheaf JY' OY')
        (RingedSite.ofCommRingSheaf JY OY) f h' h g := sorry

variable [HasWeakSheafify JX CommRingCat.{u}]
variable [HasWeakSheafify JX AddCommGrpCat.{u}]
variable [JX.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify JX' CommRingCat.{u}]
variable [HasWeakSheafify JX' AddCommGrpCat.{u}]
variable [JX'.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The section map obtained by applying the upper structure-sheaf map and then the universal
differential at the upper-left corner.  Its codomain is kept as the pushed-forward module, so
restriction of scalars is available without a local module instance. -/
@[stacks 04BR "section formula"]
noncomputable def comparisonSection {U : CXᵒᵖ} (t : OX.obj.obj U) :
    ((SheafOfModules.pushforward f.structureSheafMap).obj
      (relativeDifferentials (inverseImageStructureSheafMap h'))).val.obj U :=
  (relativeDifferential (inverseImageStructureSheafMap h')).d
    (f.structureSheafMap.hom.app U t)

/-- Additivity of the section map underlying the pullback comparison derivation. -/
theorem comparison_add {U : CXᵒᵖ} (a b : OX.obj.obj U) :
    comparisonSection f h' (a + b) =
      comparisonSection f h' a + comparisonSection f h' b := sorry

/-- The Leibniz rule for the section map underlying the pullback comparison derivation. -/
theorem comparison_mul {U : CXᵒᵖ} (a b : OX.obj.obj U) :
    comparisonSection f h' (a * b) =
      a • comparisonSection f h' b + b • comparisonSection f h' a := sorry

/-- Naturality of the section map underlying the pullback comparison derivation. -/
theorem comparison_naturality {U V : CXᵒᵖ} (rho : U ⟶ V) (t : OX.obj.obj U) :
    comparisonSection f h' (OX.obj.map rho t) =
      (((SheafOfModules.pushforward f.structureSheafMap).obj
          (relativeDifferentials (inverseImageStructureSheafMap h'))).val.map rho)
        (comparisonSection f h' t) := sorry

/-- Commutativity of the ringed-site square makes the pulled differential vanish on the base
structure sheaf. -/
theorem comparison_base
    (sq : Commutes f g h h') {U : CXᵒᵖ}
    (a : ((h.base.sheafPullback CommRingCat.{u} JY JX).obj OY).obj.obj U) :
    comparisonSection f h' ((inverseImageStructureSheafMap h).hom.app U a) = 0 := sorry

/-- The relative derivation obtained by applying the upper structure-sheaf map and then the
universal differential on the upper-left corner. -/
@[stacks 04BR "comparison derivation"]
noncomputable def comparisonDerivation
    (sq : Commutes f g h h') :
    SheafOfModules.RelativeDerivation (inverseImageStructureSheafMap h)
      ((SheafOfModules.pushforward f.structureSheafMap).obj
        (relativeDifferentials (inverseImageStructureSheafMap h'))) where
  d {U} := AddMonoidHom.mk'
    (comparisonSection f h')
    (comparison_add f h')
  d_mul := comparison_mul f h'
  d_map := comparison_naturality f h'
  d_app := comparison_base f g h h' sq

/-- Evaluation formula for the derivation underlying the comparison map. -/
theorem comparisonDerivation_d
    (sq : Commutes f g h h') {U : CXᵒᵖ} (t : OX.obj.obj U) :
    (comparisonDerivation f g h h' sq).d t =
      comparisonSection f h' t := sorry

/-- The adjoint morphism from relative differentials to the pushed-forward target
differentials. -/
@[stacks 04BR "adjoint comparison morphism"]
noncomputable def comparisonAdjoint
    (sq : Commutes f g h h') :
    relativeDifferentials (inverseImageStructureSheafMap h) ⟶
      (SheafOfModules.pushforward f.structureSheafMap).obj
        (relativeDifferentials (inverseImageStructureSheafMap h')) :=
  relativeDifferentialDesc (inverseImageStructureSheafMap h)
    (comparisonDerivation f g h h' sq)

/-- The canonical pullback comparison morphism for relative differentials attached to a
commutative square of ringed-site morphisms. -/
@[stacks 04BR "comparison morphism"]
noncomputable def comparison
    (sq : Commutes f g h h') :
    (SheafOfModules.pullback f.structureSheafMap).obj
        (relativeDifferentials (inverseImageStructureSheafMap h)) ⟶
      relativeDifferentials (inverseImageStructureSheafMap h') :=
  (comparisonDerivation f g h h' sq).pullbackDesc

/-- A morphism is the differential comparison when its adjoint carries each universal
differential to the differential of the pulled section. -/
def IsComparison
    (tau : (SheafOfModules.pullback f.structureSheafMap).obj
        (relativeDifferentials (inverseImageStructureSheafMap h)) ⟶
      relativeDifferentials (inverseImageStructureSheafMap h')) : Prop :=
  ∀ {U : CXᵒᵖ} (t : OX.obj.obj U),
    ((SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap).homEquiv _ _
        tau).val.app U
        ((relativeDifferential (inverseImageStructureSheafMap h)).d t) =
      comparisonSection f h' t

/-- The sectionwise comparison property is equivalent to the generic universal pullback descent
property. -/
theorem isComparison_iff_isPullbackDesc
    (sq : Commutes f g h h')
    (tau : (SheafOfModules.pullback f.structureSheafMap).obj
        (relativeDifferentials (inverseImageStructureSheafMap h)) ⟶
      relativeDifferentials (inverseImageStructureSheafMap h')) :
    IsComparison f h h' tau ↔
      (comparisonDerivation f g h h' sq).IsPullbackDesc tau := sorry

/-- The canonical comparison satisfies its sectionwise characterization. -/
theorem comparison_isComparison
    (sq : Commutes f g h h') :
    IsComparison f h h' (comparison f g h h' sq) := sorry

/-- The adjoint of the comparison carries the universal differential of `t` to the differential
of its image under the upper structure-sheaf map. -/
theorem comparison_d
    (sq : Commutes f g h h') {U : CXᵒᵖ} (t : OX.obj.obj U) :
    ((SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap).homEquiv _ _
        (comparison f g h h' sq)).val.app U
        ((relativeDifferential (inverseImageStructureSheafMap h)).d t) =
      comparisonSection f h' t := sorry

/-- A morphism satisfying the sectionwise characterization equals the canonical comparison. -/
theorem eq_comparison
    (sq : Commutes f g h h')
    {tau : (SheafOfModules.pullback f.structureSheafMap).obj
        (relativeDifferentials (inverseImageStructureSheafMap h)) ⟶
      relativeDifferentials (inverseImageStructureSheafMap h')}
    (h_tau : IsComparison f h h' tau) :
    tau = comparison f g h h' sq := sorry

/-- Lemma 18.33.11 (04BR): a commutative square of ringed topoi presented by ringed sites has a
unique pullback comparison morphism on relative differentials. -/
@[stacks 04BR]
theorem existsUnique_comparison
    (sq : Commutes f g h h') :
    ∃! tau : (SheafOfModules.pullback f.structureSheafMap).obj
        (relativeDifferentials (inverseImageStructureSheafMap h)) ⟶
      relativeDifferentials (inverseImageStructureSheafMap h'),
      IsComparison f h h' tau := sorry

end RingedSite.Hom.Differentials

-- `comparisonSection` is the explicit non-Prop payload.  Any `sorryAx` reported for the
-- derivation and the descended comparison is confined to its Prop-valued additivity, Leibniz,
-- naturality, and base-vanishing laws.
