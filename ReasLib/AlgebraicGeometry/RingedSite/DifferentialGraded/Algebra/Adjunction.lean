module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Algebra.Functor
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward.Complex.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential graded algebras on ringed-site presentations

Pullback and pushforward of differential graded algebras are obtained from the canonical monoidal
adjunction on unbounded cochain complexes.  This file owns the site-presented construction; its
definitions do not rebuild homogeneous multiplication or unit maps.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom

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

variable (f : Hom (RingedSite.ofCommRingSheaf JX OX)
  (RingedSite.ofCommRingSheaf JY OY))
variable [(PresheafOfModules.pushforward.{w} f.structureSheafMap.hom).IsRightAdjoint]

/-- Pullback of differential graded algebras along a ringed-site presentation. -/
@[stacks 0FRE "site-presented pullback of differential graded algebras"]
noncomputable def pullbackDGA : DGA(OY) ⥤ DGA(OX) :=
  SheafOfModules.RingedSite.DifferentialGradedAlgebra.map
    (C := CY) (D := CX) (JC := JY) (JD := JX) (OC := OY) (OD := OX)
    f.modulePullbackComplex.{w}

/-- Pushforward of differential graded algebras along a ringed-site presentation. -/
@[stacks 0FRE "site-presented pushforward of differential graded algebras"]
noncomputable def pushforwardDGA : DGA(OX) ⥤ DGA(OY) :=
  SheafOfModules.RingedSite.DifferentialGradedAlgebra.map
    (C := CX) (D := CY) (JC := JX) (JD := JY) (OC := OX) (OD := OY)
    f.modulePushforwardComplex.{w}

/-- Pullback is left adjoint to pushforward for differential graded algebras on ringed-site
presentations. -/
@[stacks 0FRE "site-presented differential graded algebra adjunction"]
noncomputable def pullbackPushforwardDGAAdjunction :
    f.pullbackDGA ⊣ f.pushforwardDGA :=
  SheafOfModules.RingedSite.DifferentialGradedAlgebra.mapAdjunction
    (C := CY) (D := CX) (JC := JY) (JD := JX) (OC := OY) (OD := OX)
    f.modulePushforwardComplex.{w}
    (modulePullbackPushforwardComplexAdjunction.{w} f)

/-- The unit component of the differential graded algebra pullback-pushforward adjunction. -/
@[stacks 0FRE "site-presented differential graded algebra unit"]
noncomputable abbrev pullbackPushforwardDGAUnit (A : DGA(OY)) :
    A ⟶ f.pushforwardDGA.obj (f.pullbackDGA.obj A) :=
  f.pullbackPushforwardDGAAdjunction.unit.app A

/-- The counit component of the differential graded algebra pullback-pushforward adjunction. -/
@[stacks 0FRE "site-presented differential graded algebra counit"]
noncomputable abbrev pullbackPushforwardDGACounit (A : DGA(OX)) :
    f.pullbackDGA.obj (f.pushforwardDGA.obj A) ⟶ A :=
  f.pullbackPushforwardDGAAdjunction.counit.app A

/-- The Hom equivalence induced by the differential graded algebra pullback-pushforward
adjunction. -/
@[stacks 0FRE "site-presented differential graded algebra Hom equivalence"]
noncomputable def pullbackDGAHomEquiv (A : DGA(OY)) (B : DGA(OX)) :
    (f.pullbackDGA.obj A ⟶ B) ≃ (A ⟶ f.pushforwardDGA.obj B) :=
  f.pullbackPushforwardDGAAdjunction.homEquiv A B

/-- The underlying cochain complex of a pulled-back differential graded algebra is its degreewise
module pullback. -/
@[simp]
theorem pullbackDGA_obj_toComplex (A : DGA(OY)) :
    (f.pullbackDGA.obj A).toComplex =
      f.modulePullbackComplex.{w}.obj A.toComplex := sorry

/-- The underlying cochain complex of a pushed-forward differential graded algebra is its
degreewise module pushforward. -/
@[simp]
theorem pushforwardDGA_obj_toComplex (A : DGA(OX)) :
    (f.pushforwardDGA.obj A).toComplex =
      f.modulePushforwardComplex.{w}.obj A.toComplex := sorry

end RingedSite.Hom
