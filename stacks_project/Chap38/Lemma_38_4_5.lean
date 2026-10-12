/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissageAtAmbientPoint.BaseChange
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 38.4.5: affine pointed base change through an isomorphism on residue fields
transports an ambient-point one-step dévissage and its distinguished lifted points. -/
@[stacks 05H8]
#check (AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint.baseChange :
  {S S' : AlgebraicGeometry.Scheme.{u}} → {X : Over S} →
    {F : X.left.Modules} →
      [hX : AlgebraicGeometry.LocallyOfFiniteType X.hom] →
        [hFqc : F.IsQuasicoherent] → [hFft : F.IsFiniteType] → {x : X.left} →
          (D : AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint X F x) →
            (g : S' ⟶ S) → (s' : S') → g s' = X.hom x →
              [AlgebraicGeometry.IsAffine S'] → [IsIso (g.residueFieldMap s')] →
                (x' : (CategoryTheory.Limits.pullback X.hom g :
                  AlgebraicGeometry.Scheme)) →
                  pullback.fst X.hom g x' = x →
                    pullback.snd X.hom g x' = s' →
                      (z' : (CategoryTheory.Limits.pullback
                        D.toOneStepDevissage.Z.hom g : AlgebraicGeometry.Scheme)) →
                        pullback.fst D.toOneStepDevissage.Z.hom g z' = D.z →
                          pullback.snd D.toOneStepDevissage.Z.hom g z' = s' →
                            (y' : (CategoryTheory.Limits.pullback
                              D.toOneStepDevissage.Y.hom g :
                                AlgebraicGeometry.Scheme)) →
                              pullback.fst D.toOneStepDevissage.Y.hom g y' = D.y →
                                pullback.snd D.toOneStepDevissage.Y.hom g y' = s' →
                                  @AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint
                                    S' ((Over.pullback g).obj X)
                                    (AlgebraicGeometry.Scheme.Modules.baseChangeModule
                                      X.hom g F :
                                        ((Over.pullback g).obj X).left.Modules)
                                    (@AlgebraicGeometry.Scheme.Modules.OneStepDevissage.baseChange_locallyOfFiniteType
                                      S S' X g hX)
                                    (@AlgebraicGeometry.Scheme.Modules.OneStepDevissage.baseChangeModule_isQuasicoherent
                                      S S' X F g hFqc)
                                    (@AlgebraicGeometry.Scheme.Modules.OneStepDevissage.baseChangeModule_isFiniteType
                                      S S' X F g hFft) x')
