/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.BaseChange
public import ReasLib.CategoryTheory.Monoidal.Bimod.ChangeOfScalars.Adjunction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base-change adjunction for differential graded module sheaves

A monoidal adjunction `F ⊣ G` and a differential graded algebra morphism `F(A) ⟶ B`
determine both sides of a module adjunction.  Pullback is extension of scalars after transport
by `F`; pushforward transports by `G` and restricts scalars along the adjoint mate
`A ⟶ G(B)`.  The construction is transported through the canonical equivalence between
differential graded modules and right module objects.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe uC vC wC uD vD wD

namespace SheafOfModules.RingedSite.DifferentialGradedModule.BaseChange

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{wC} RingCat.{wC})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{wD} RingCat.{wD})]
variable [HasWeakSheafify JC AddCommGrpCat.{wC}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{wC}]
variable [HasWeakSheafify JD AddCommGrpCat.{wD}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{wD}]
variable [UnivLE.{max uC vC, wC}] [UnivLE.{max uD vD, wD}]
variable {OC : Sheaf JC CommRingCat.{wC}} {OD : Sheaf JD CommRingCat.{wD}}

variable {F : CochainComplex
    (DifferentialGradedAlgebra.moduleCategory (J := JC) (𝒪 := OC)) ℤ ⥤
  CochainComplex
    (DifferentialGradedAlgebra.moduleCategory (J := JD) (𝒪 := OD)) ℤ}
variable {G : CochainComplex
    (DifferentialGradedAlgebra.moduleCategory (J := JD) (𝒪 := OD)) ℤ ⥤
  CochainComplex
    (DifferentialGradedAlgebra.moduleCategory (J := JC) (𝒪 := OC)) ℤ}
variable (adj : F ⊣ G)
variable [F.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal]

/-- The differential graded algebra mate of `φ : F(A) ⟶ B` under the lifted monoidal
adjunction. -/
@[stacks 0FRU "differential graded algebra mate"]
noncomputable def mate {A : DGA(OC)} {B : DGA(OD)}
    (φ : (DifferentialGradedAlgebra.map F).obj A ⟶ B) :
    A ⟶ (DifferentialGradedAlgebra.map G).obj B :=
  DifferentialGradedAlgebra.mapHomEquiv G adj A B φ

/-- Passing the differential graded algebra mate to monoid objects gives the monoid-level
mate of the coefficient morphism. -/
theorem mate_toMon {A : DGA(OC)} {B : DGA(OD)}
    (φ : (DifferentialGradedAlgebra.map F).obj A ⟶ B) :
    (DifferentialGradedAlgebra.toMonFunctor (𝒪 := OC)).map (mate adj φ) ≫
        (DifferentialGradedAlgebra.toMonCounitIso
          (𝒪 := OC) (G.mapMon.obj B.toMon)).hom =
      adj.rightModuleMate (DifferentialGradedAlgebra.mapHomToMon F φ) := sorry

/-- Pushforward of right differential graded modules associated to
`φ : F(A) ⟶ B`: pass to right module objects, transport by `G`, restrict along the
adjoint mate of `φ`, and return to homogeneous differential graded modules. -/
@[stacks 0FRU "differential graded module pushforward"]
noncomputable def pushforward {A : DGA(OC)} {B : DGA(OD)}
    (φ : (DifferentialGradedAlgebra.map F).obj A ⟶ B) :
    Mod(B, d) ⥤ Mod(A, d) :=
  toBimodFunctor B ⋙
    adj.baseChangeRightPushforward
      (DifferentialGradedAlgebra.mapHomToMon F φ) ⋙
    ofBimodFunctor A

/-- Evaluating DG pushforward is transport of the corresponding right module object followed
by restriction along the coefficient mate. -/
@[simp]
theorem pushforward_obj {A : DGA(OC)} {B : DGA(OD)}
    (φ : (DifferentialGradedAlgebra.map F).obj A ⟶ B) (N : Mod(B, d)) :
    (pushforward adj φ).obj N =
      ofBimod ((adj.baseChangeRightPushforward
        (DifferentialGradedAlgebra.mapHomToMon F φ)).obj (toBimod N)) := sorry

/-- Differential graded module base change along `φ : F(A) ⟶ B` is left adjoint to
the explicit pushforward along its adjoint mate. -/
@[stacks 0FRU "differential graded module base-change adjunction"]
noncomputable def adjunction {A : DGA(OC)} {B : DGA(OD)}
    (φ : (DifferentialGradedAlgebra.map F).obj A ⟶ B) :
    DifferentialGradedModule.baseChange F φ ⊣ pushforward adj φ :=
  ((toBimodEquivalence A).toAdjunction.comp
    (adj.baseChangeRightAdjunction
      (DifferentialGradedAlgebra.mapHomToMon F φ))).comp
    (toBimodEquivalence B).symm.toAdjunction

/-- The standardly oriented Hom equivalence for differential graded module base change. -/
@[stacks 0FRU "differential graded module base-change Hom equivalence"]
noncomputable def homEquiv {A : DGA(OC)} {B : DGA(OD)}
    (φ : (DifferentialGradedAlgebra.map F).obj A ⟶ B)
    (M : Mod(A, d)) (N : Mod(B, d)) :
    ((DifferentialGradedModule.baseChange F φ).obj M ⟶ N) ≃
      (M ⟶ (pushforward adj φ).obj N) :=
  (adjunction adj φ).homEquiv M N

/-- Lemma 24.18.1 (0FRU), general form: maps into DG pushforward correspond canonically to
maps out of DG pullback. -/
@[stacks 0FRU "differential graded pullback-pushforward Hom equivalence"]
noncomputable def pullbackPushforwardHomEquiv
    {A : DGA(OC)} {B : DGA(OD)}
    (φ : (DifferentialGradedAlgebra.map F).obj A ⟶ B)
    (M : Mod(A, d)) (N : Mod(B, d)) :
    (M ⟶ (pushforward adj φ).obj N) ≃
      ((DifferentialGradedModule.baseChange F φ).obj M ⟶ N) :=
  (homEquiv adj φ M N).symm

end SheafOfModules.RingedSite.DifferentialGradedModule.BaseChange

end
