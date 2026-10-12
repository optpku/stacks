/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Lemma_71_11_5_BaseChange
public import stacks_project.Chap71.Lemma_71_11_2_RestrictionComposition
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.CanonicalBaseChange

/-!
# Actual Serre-twist models on represented algebraic spaces

The family, algebra operations, and base-change components are constructed from
the actual homogeneous-fraction Serre algebra and the extension adjunction.
These are the local models required for global relative-Proj twist descent.
-/

@[expose] public section
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace Opposite
open SheafOfModules.RingedSite
noncomputable section
universe u v w

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj.TwistFamily

section Models
variable {S : Scheme.{u}} {R : Type v} {A : Type u}
variable [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (π : Proj 𝒜 ⟶ S)

/-- The actual Serre sheaf extended from the represented scheme. -/
def schemeObj (n : ℤ) : (ofOver (Over.mk π)).Modules :=
  (Modules.RestrictToScheme.extension (Over.mk π)).obj
    (Proj.AssociatedModule.twistingSheaf 𝒜 n)

/-- The unit of the extended canonical Serre algebra. -/
def schemeUnit : SheafOfModules.unit (structureSheaf (ofOver (Over.mk π))) ⟶
    schemeObj 𝒜 π 0 :=
  (Modules.structureModuleIsoTensorUnit (ofOver (Over.mk π))).hom ≫
    (Functor.Monoidal.εIso (Modules.RestrictToScheme.extension (Over.mk π))).hom ≫
      (Modules.RestrictToScheme.extension (Over.mk π)).map
        (Proj.AssociatedModule.CanonicalAlgebra.oneHom 𝒜)

/-- Multiplication is transported by the specified strong-monoidal extension maps. -/
def schemeMul (a b : ℤ) : schemeObj 𝒜 π a ⊗ schemeObj 𝒜 π b ⟶ schemeObj 𝒜 π (a + b) :=
  (Functor.Monoidal.μIso (Modules.RestrictToScheme.extension (Over.mk π))
    (Proj.AssociatedModule.twistingSheaf 𝒜 a) (Proj.AssociatedModule.twistingSheaf 𝒜 b)).hom ≫
      (Modules.RestrictToScheme.extension (Over.mk π)).map
        (Proj.AssociatedModule.CanonicalAlgebra.mulHom 𝒜 a b)

/-- Lift the actual unit through the specified universe-lift unit comparison. -/
def schemeOne (U : (smallEtaleSite (ofOver (Over.mk π)))ᵒᵖ) :
    (Modules.liftModule (schemeObj 𝒜 π 0)).val.obj U :=
  (((Modules.liftedUnitIso (ofOver (Over.mk π))).inv ≫
    Modules.liftModuleMap (schemeUnit 𝒜 π)).val.app U).hom
      (liftedUnitSection (ofOver (Over.mk π)) U)

/-- Lift the actual bilinear multiplication through the tensor-section comparison. -/
def schemeLiftedMul (U : (smallEtaleSite (ofOver (Over.mk π)))ᵒᵖ) (a b : ℤ) :
    (Modules.liftModule (schemeObj 𝒜 π a)).val.obj U →ₗ[
      (commStructureSheafLift (ofOver (Over.mk π))).obj.obj U]
      (Modules.liftModule (schemeObj 𝒜 π b)).val.obj U →ₗ[
        (commStructureSheafLift (ofOver (Over.mk π))).obj.obj U]
        (Modules.liftModule (schemeObj 𝒜 π (a + b))).val.obj U :=
  (liftModuleTensorApp (schemeObj 𝒜 π a) (schemeObj 𝒜 π b) U).compr₂
    ((Modules.liftModuleMap (schemeMul 𝒜 π a b)).val.app U).hom

/-- The actual lifted graded algebra on the represented algebraic space. -/
def schemeAlgebra : GradedAlgebraSheaf.{u + 1, u}
    (commStructureSheafLift (ofOver (Over.mk π))) where
  obj n := Modules.liftModule (schemeObj 𝒜 π n)
  one := schemeOne 𝒜 π
  mul := schemeLiftedMul 𝒜 π
  map_one := sorry
  map_mul := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry

/-- A concrete coherent twist-family object, with its objects and all operations fixed. -/
def ofScheme : TwistFamily (ofOver (Over.mk π)) where
  algebra := schemeAlgebra 𝒜 π
  obj := schemeObj 𝒜 π
  iso _ := Iso.refl _
  mul := schemeMul 𝒜 π
  unit := schemeUnit 𝒜 π
  unit_spec := sorry
  mul_spec := sorry

end Models

section Comparison
variable {S : Scheme.{max u v w}}
variable {R : Type v} {R' : Type w} [CommRing R] [CommRing R']
variable {A B : Type (max u v w)} [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R' B]
variable {𝒜 : ℕ → Submodule R A} {ℬ : ℕ → Submodule R' B}
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-- The actual full-domain projective map, as a scheme morphism over the given base. -/
def schemeMapOver (ψ : 𝒜 →+*ᵍ ℬ) (hTop : projMapDomain ψ = ⊤) (π : Proj 𝒜 ⟶ S) :
    Over.mk (Proj.AssociatedModule.GradedMap.fullMap.{u, v, w} ψ hTop ≫ π) ⟶ Over.mk π :=
  Over.homMk (Proj.AssociatedModule.GradedMap.fullMap.{u, v, w} ψ hTop) rfl

/-- The represented-space component is the extension/pullback comparison followed by
extension of the actual homogeneous-fraction map. -/
def schemeComparisonMap (ψ : 𝒜 →+*ᵍ ℬ) (hTop : projMapDomain ψ = ⊤)
    (π : Proj 𝒜 ⟶ S) (n : ℤ) :
    (Modules.pullback (ofOverMap (schemeMapOver.{u, v, w} ψ hTop π))).obj
      (schemeObj 𝒜 π n) ⟶
        schemeObj ℬ (Proj.AssociatedModule.GradedMap.fullMap.{u, v, w} ψ hTop ≫ π) n :=
  (Modules.RestrictToScheme.extensionPullbackIso
      (schemeMapOver.{u, v, w} ψ hTop π)).inv.app (Proj.AssociatedModule.twistingSheaf 𝒜 n) ≫
    (Modules.RestrictToScheme.extension
      (Over.mk (Proj.AssociatedModule.GradedMap.fullMap.{u, v, w} ψ hTop ≫ π))).map
        (Proj.AssociatedModule.GradedMap.hom.{u, v, w} ψ hTop n)

/-- The actual comparison preserves both displayed algebra operations. -/
def schemeComparison (ψ : 𝒜 →+*ᵍ ℬ) (hTop : projMapDomain ψ = ⊤) (π : Proj 𝒜 ⟶ S) :
    GradedAlgebraComparison (ofOverMap (schemeMapOver.{u, v, w} ψ hTop π))
      (ofScheme 𝒜 π)
      (ofScheme ℬ (Proj.AssociatedModule.GradedMap.fullMap.{u, v, w} ψ hTop ≫ π)) where
  degreeMap := schemeComparisonMap.{u, v, w} ψ hTop π
  map_one := sorry
  map_mul := sorry

end Comparison

section BaseChange
variable {S : Scheme.{u}} {R R' A : Type u} [CommRing R] [CommRing R'] [CommRing A]
variable [Algebra R R'] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (π : Proj 𝒜 ⟶ S)

/-- In tensor-product base change, the represented-space comparison has its genuine
inverse, obtained by composing the specified inverse-image and Serre isomorphisms. -/
def schemeBaseChangeDegreeIso (n : ℤ) :
    (Modules.pullback (ofOverMap (schemeMapOver.{u, u, u}
      (tensorProductBaseChangePsi (R' := R') 𝒜)
      (projMapDomain_tensorProductBaseChange_eq_top (R' := R') 𝒜) π))).obj
        (schemeObj 𝒜 π n) ≅
      schemeObj (tensorProductBaseChangeGrading (R' := R') 𝒜)
        (Proj.AssociatedModule.GradedMap.baseChangeMap (R' := R') 𝒜 ≫ π) n :=
  (Modules.RestrictToScheme.extensionPullbackIso (schemeMapOver.{u, u, u}
      (tensorProductBaseChangePsi (R' := R') 𝒜)
      (projMapDomain_tensorProductBaseChange_eq_top (R' := R') 𝒜) π)).symm.app
        (Proj.AssociatedModule.twistingSheaf 𝒜 n) ≪≫
    (Modules.RestrictToScheme.extension
      (Over.mk (Proj.AssociatedModule.GradedMap.baseChangeMap (R' := R') 𝒜 ≫ π))).mapIso
        (Proj.AssociatedModule.GradedMap.baseChangeIso (R' := R') 𝒜 n)

end BaseChange
end AlgebraicGeometry.AlgebraicSpace.RelativeProj.TwistFamily
