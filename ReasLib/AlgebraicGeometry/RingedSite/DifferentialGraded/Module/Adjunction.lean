module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.BaseChange.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.DifferentialGraded.Algebra.Adjunction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback and pushforward of differential graded modules on ringed sites

For a morphism `f` of commutative ringed-site presentations and a morphism
`φ : f^*(ℬ) ⟶ 𝒜` of differential graded algebras, this file specializes the generic
monoidal base-change adjunction.  The resulting pullback and pushforward functors are determined
by `f` and `φ`; no caller-supplied module functors or adjunction data remain.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom.DGModule

variable {CX : Type uX} [Category.{vX} CX]
variable {CY : Type uY} [Category.{vY} CY]
variable {JX : GrothendieckTopology CX} {JY : GrothendieckTopology CY}
variable [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify JX AddCommGrpCat.{w}]
variable [JX.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JY AddCommGrpCat.{w}]
variable [JY.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}

variable (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JX OX)
  (RingedSite.ofCommRingSheaf JY OY))
variable [(PresheafOfModules.pushforward.{w} f.structureSheafMap.hom).IsRightAdjoint]

/-- The canonical monoidal adjunction on unbounded complexes used by DG module base change. -/
@[stacks 0FRU "complex adjunction underlying differential graded base change"]
noncomputable abbrev complexAdjunction :=
  RingedSite.Hom.modulePullbackPushforwardComplexAdjunction.{w} f

/-- The direct-image-form DGA morphism `ℬ ⟶ f_*𝒜` adjoint to
`φ : f^*ℬ ⟶ 𝒜`. -/
@[stacks 0FRU "direct-image mate of a differential graded algebra morphism"]
noncomputable def mate {A : DGA(OX)} {B : DGA(OY)}
    (φ : f.pullbackDGA.obj B ⟶ A) : B ⟶ f.pushforwardDGA.obj A :=
  SheafOfModules.RingedSite.DifferentialGradedModule.BaseChange.mate
    (complexAdjunction f) φ

/-- Pullback of right DG `ℬ`-modules along `φ : f^*ℬ ⟶ 𝒜`. -/
@[stacks 0FRU "pullback of differential graded modules"]
noncomputable def pullback {A : DGA(OX)} {B : DGA(OY)}
    (φ : f.pullbackDGA.obj B ⟶ A) : Mod(B, d) ⥤ Mod(A, d) :=
  SheafOfModules.RingedSite.DifferentialGradedModule.baseChange
    f.modulePullbackComplex.{w} φ

/-- Pushforward of right DG `𝒜`-modules, with the `ℬ`-action induced by the mate
`ℬ ⟶ f_*𝒜` of `φ`. -/
@[stacks 0FRU "pushforward of differential graded modules"]
noncomputable def pushforward {A : DGA(OX)} {B : DGA(OY)}
    (φ : f.pullbackDGA.obj B ⟶ A) : Mod(A, d) ⥤ Mod(B, d) :=
  SheafOfModules.RingedSite.DifferentialGradedModule.BaseChange.pushforward
    (complexAdjunction f) φ

/-- Pullback of differential graded modules along `φ` is left adjoint to pushforward with
the module structure induced by its mate. -/
@[stacks 0FRU "ringed-site differential graded module adjunction"]
noncomputable def adjunction {A : DGA(OX)} {B : DGA(OY)}
    (φ : f.pullbackDGA.obj B ⟶ A) : pullback f φ ⊣ pushforward f φ :=
  SheafOfModules.RingedSite.DifferentialGradedModule.BaseChange.adjunction
    (complexAdjunction f) φ

/-- Lemma 24.18.1 (0FRU): maps from a DG `ℬ`-module into pushforward correspond
canonically to maps from its pullback into the original DG `𝒜`-module. -/
@[stacks 0FRU "ringed-site differential graded pullback-pushforward Hom equivalence"]
noncomputable def homEquiv {A : DGA(OX)} {B : DGA(OY)}
    (φ : f.pullbackDGA.obj B ⟶ A) (N : Mod(B, d)) (M : Mod(A, d)) :
    (N ⟶ (pushforward f φ).obj M) ≃ ((pullback f φ).obj N ⟶ M) :=
  SheafOfModules.RingedSite.DifferentialGradedModule.BaseChange.pullbackPushforwardHomEquiv
    (complexAdjunction f) φ N M

end RingedSite.Hom.DGModule

end
