module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Algebra.Functor
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Pullback.Complex.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential graded algebras along morphisms of ringed topoi

Pullback and pushforward of differential graded algebras along an arbitrary morphism of ringed
topoi are obtained from the monoidal adjunction on unbounded cochain complexes.  Homogeneous
multiplication and unit maps are transported by `DGA.map` rather than rebuilt.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra

noncomputable section

universe uX vX uY vY w

namespace RingedSite.ToposHom

variable {CX : Type uX} [Category.{vX} CX]
variable {CY : Type uY} [Category.{vY} CY]
variable {JX : GrothendieckTopology CX} {JY : GrothendieckTopology CY}
variable [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JX.HasSheafCompose (forget RingCat.{w})]
variable [JY.HasSheafCompose (forget RingCat.{w})]
variable [HasWeakSheafify JX AddCommGrpCat.{w}]
variable [JX.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JY AddCommGrpCat.{w}]
variable [JY.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}
variable (f : ToposHom (ofCommRingSheaf JX OX) (ofCommRingSheaf JY OY))
variable [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]

/-- Pullback of differential graded algebras along a morphism of ringed topoi. -/
noncomputable def pullbackDGA : DGA(OY) ⥤ DGA(OX) :=
  @SheafOfModules.RingedSite.DifferentialGradedAlgebra.map
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ OY OX f.modulePullbackComplex
    (modulePullbackComplex.monoidal f).toLaxMonoidal

/-- Pushforward of differential graded algebras along a morphism of ringed topoi. -/
noncomputable def pushforwardDGA : DGA(OX) ⥤ DGA(OY) :=
  @SheafOfModules.RingedSite.DifferentialGradedAlgebra.map
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ OX OY f.modulePushforwardComplex
    (modulePushforwardComplex.laxMonoidal f)

/-- Pullback is left adjoint to pushforward for differential graded algebras on ringed topoi. -/
noncomputable def pullbackPushforwardDGAAdjunction :
    f.pullbackDGA ⊣ f.pushforwardDGA :=
  @SheafOfModules.RingedSite.DifferentialGradedAlgebra.mapAdjunction
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ OY OX
    f.modulePullbackComplex f.modulePushforwardComplex
    (modulePullbackComplex.monoidal f) (modulePushforwardComplex.laxMonoidal f)
    (modulePullbackPushforwardComplexAdjunction f)
    (modulePullbackPushforwardComplexAdjunction.isMonoidal f)

/-- The unit component of the differential graded algebra pullback-pushforward adjunction. -/
noncomputable abbrev pullbackPushforwardDGAUnit (A : DGA(OY)) :
    A ⟶ f.pushforwardDGA.obj (f.pullbackDGA.obj A) :=
  f.pullbackPushforwardDGAAdjunction.unit.app A

/-- The counit component of the differential graded algebra pullback-pushforward adjunction. -/
noncomputable abbrev pullbackPushforwardDGACounit (A : DGA(OX)) :
    f.pullbackDGA.obj (f.pushforwardDGA.obj A) ⟶ A :=
  f.pullbackPushforwardDGAAdjunction.counit.app A

/-- The Hom equivalence induced by the differential graded algebra pullback-pushforward
adjunction. -/
noncomputable def pullbackDGAHomEquiv (A : DGA(OY)) (B : DGA(OX)) :
    (f.pullbackDGA.obj A ⟶ B) ≃ (A ⟶ f.pushforwardDGA.obj B) :=
  f.pullbackPushforwardDGAAdjunction.homEquiv A B

/-- The underlying cochain complex of a pulled-back differential graded algebra is its degreewise
module pullback. -/
@[simp]
theorem pullbackDGA_obj_toComplex (A : DGA(OY)) :
    (f.pullbackDGA.obj A).toComplex =
      f.modulePullbackComplex.obj A.toComplex := sorry

/-- The underlying cochain complex of a pushed-forward differential graded algebra is its
degreewise module pushforward. -/
@[simp]
theorem pushforwardDGA_obj_toComplex (A : DGA(OX)) :
    (f.pushforwardDGA.obj A).toComplex =
      f.modulePushforwardComplex.obj A.toComplex := sorry

/-- Degree `n` of a pulled-back differential graded algebra is the module pullback of the original
degree `n` component. -/
theorem pullbackDGA_obj_X (A : DGA(OY)) (n : ℤ) :
    (f.pullbackDGA.obj A).toComplex.X n =
      f.modulePullback.obj (A.toComplex.X n) := sorry

/-- Degree `n` of a pushed-forward differential graded algebra is the module pushforward of the
original degree `n` component. -/
theorem pushforwardDGA_obj_X (A : DGA(OX)) (n : ℤ) :
    (f.pushforwardDGA.obj A).toComplex.X n =
      f.modulePushforward.obj (A.toComplex.X n) := sorry

/-- The differential of a pulled-back differential graded algebra is the module pullback of the
original differential, as a map
`f.modulePullback.obj (A.toComplex.X n) ⟶ f.modulePullback.obj (A.toComplex.X (n + 1))`. -/
theorem pullbackDGA_obj_d (A : DGA(OY)) (n : ℤ) :
    eqToHom (Eq.symm (pullbackDGA_obj_X f A n)) ≫
      (f.pullbackDGA.obj A).toComplex.d n (n + 1) ≫
      eqToHom (pullbackDGA_obj_X f A (n + 1)) =
      f.modulePullback.map (A.toComplex.d n (n + 1)) := sorry

/-- The differential of a pushed-forward differential graded algebra is the module pushforward of
the original differential, as a map
`f.modulePushforward.obj (A.toComplex.X n) ⟶ f.modulePushforward.obj (A.toComplex.X (n + 1))`. -/
theorem pushforwardDGA_obj_d (A : DGA(OX)) (n : ℤ) :
    eqToHom (Eq.symm (pushforwardDGA_obj_X f A n)) ≫
      (f.pushforwardDGA.obj A).toComplex.d n (n + 1) ≫
      eqToHom (pushforwardDGA_obj_X f A (n + 1)) =
      f.modulePushforward.map (A.toComplex.d n (n + 1)) := sorry

/-- The underlying cochain map of the differential graded algebra Hom equivalence is the
module-complex adjunction Hom equivalence, transported along `pullbackDGA_obj_toComplex` and
`pushforwardDGA_obj_toComplex`. -/
theorem pullbackDGAHomEquiv_hom (A : DGA(OY)) (B : DGA(OX))
    (φ : f.pullbackDGA.obj A ⟶ B) :
    ((f.pullbackDGAHomEquiv A B) φ).hom =
      (modulePullbackPushforwardComplexAdjunction f).homEquiv A.toComplex B.toComplex
          (eqToHom (Eq.symm (pullbackDGA_obj_toComplex f A)) ≫ φ.hom) ≫
        eqToHom (Eq.symm (pushforwardDGA_obj_toComplex f B)) := sorry

end RingedSite.ToposHom
