/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissageAtAmbientPoint
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.LocalGeneration
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support.FiberSubscheme
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Extension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Over
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.SmoothFactorization.Affine

/-!
# Existence of one-step dévissages after elementary étale refinement
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite-type quasicoherent module on a locally finite-type scheme morphism admits,
after elementary étale refinement at an ambient point, a one-step dévissage whose smooth
model has the prescribed relative dimension and geometrically integral fibres. -/
theorem exists_oneStepDevissageAtAmbientPoint_after_elementaryEtale {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (ℱ : X.Modules)
    [h_quasicoherent : ℱ.IsQuasicoherent] [h_finiteType : ℱ.IsFiniteType] (x : X)
    (n : ℕ) (h_dim : ambientFiberSupportDimensionAt f ℱ x = (n : WithBot ℕ∞)) :
    ∃ U : EtaleNeighborhood.Elementary X x,
      let X' := U.obj
      let ℱ' := (Scheme.Modules.pullback X'.toEtale.hom).obj ℱ
      let h_quasicoherent' : ℱ'.IsQuasicoherent :=
        @pullback_isQuasicoherent _ _ X'.toEtale.hom ℱ h_quasicoherent
      let h_finiteType' : ℱ'.IsFiniteType :=
        @pullback_isFiniteType _ _ X'.toEtale.hom ℱ h_finiteType
      ∃ V : EtaleNeighborhood.Elementary S (f x),
        let S' := V.obj
        ∃ f' : X'.toEtale.left ⟶ S'.toEtale.left,
          ∃ (_ : CommSq X'.toEtale.hom f' f S'.toEtale.hom)
            (_ : f' X'.point = S'.point)
            (h_refined_finiteType : LocallyOfFiniteType (Over.mk f').hom),
            ∃ D : @OneStepDevissageAtAmbientPoint _ (Over.mk f') ℱ'
                h_refined_finiteType h_quasicoherent' h_finiteType' X'.point,
              let E := @OneStepDevissageAtAmbientPoint.toOneStepDevissage _ (Over.mk f') ℱ'
                h_refined_finiteType h_quasicoherent' h_finiteType' X'.point D
              let Y := @OneStepDevissage.Y _ (Over.mk f') ℱ' h_refined_finiteType
                h_quasicoherent' h_finiteType' ((Over.mk f').hom X'.point) E
              SmoothOfRelativeDimension n Y.hom ∧ GeometricallyIntegral Y.hom := sorry

/-- A finite-type quasicoherent module on a locally finite-type scheme morphism admits a
one-step dévissage after elementary étale refinement at any ambient point. -/
theorem exists_oneStepDevissageAtAmbientPoint {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (ℱ : X.Modules) [h_quasicoherent : ℱ.IsQuasicoherent]
    [h_finiteType : ℱ.IsFiniteType] (x : X) :
    ∃ U : EtaleNeighborhood.Elementary X x,
      let X' := U.obj
      let ℱ' := (Scheme.Modules.pullback X'.toEtale.hom).obj ℱ
      let h_quasicoherent' : ℱ'.IsQuasicoherent :=
        @pullback_isQuasicoherent _ _ X'.toEtale.hom ℱ h_quasicoherent
      let h_finiteType' : ℱ'.IsFiniteType :=
        @pullback_isFiniteType _ _ X'.toEtale.hom ℱ h_finiteType
      ∃ V : EtaleNeighborhood.Elementary S (f x),
        let S' := V.obj
        ∃ f' : X'.toEtale.left ⟶ S'.toEtale.left,
          ∃ (_ : CommSq X'.toEtale.hom f' f S'.toEtale.hom)
            (_ : f' X'.point = S'.point)
            (h_refined_finiteType : LocallyOfFiniteType (Over.mk f').hom),
            Nonempty (@OneStepDevissageAtAmbientPoint _ (Over.mk f') ℱ'
              h_refined_finiteType h_quasicoherent' h_finiteType' X'.point) := sorry

end AlgebraicGeometry.Scheme.Modules
