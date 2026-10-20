module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Injective
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Injective
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open ComplexShape

noncomputable section

universe u

/- Lemma 59.99.1 (1): inverse image from the big étale site to `Tₑₜ` along an arbitrary scheme
morphism preserves injective abelian sheaves. -/
@[stacks 0758] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.relocalization_preservesInjective :
    ∀ {S T : Scheme.{u}} (f : T ⟶ S)
      [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
      [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
      (I : Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})
      [Injective I],
      Injective
        (((AlgebraicGeometry.Scheme.Etale.SmallToBig.relocalizationFunctor f).sheafPushforwardContinuous
            AddCommGrpCat.{u} T.smallEtaleTopology
            (S.overGrothendieckTopology @Etale)).obj I))

/- Lemma 59.99.1 (2): restriction from the big étale site to `Sₑₜ` preserves injective abelian
sheaves. -/
@[stacks 0758] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.relocalization_restriction_preservesInjective :
    ∀ (S : Scheme.{u})
      [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
      [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
      (I : Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})
      [Injective I],
      Injective
        (((AlgebraicGeometry.Scheme.Etale.SmallToBig.relocalizationFunctor (𝟙 S)).sheafPushforwardContinuous
            AddCommGrpCat.{u} S.smallEtaleTopology
            (S.overGrothendieckTopology @Etale)).obj I))

/- Lemma 59.99.1 (3): inverse image from the big étale site to `Tₑₜ` along an arbitrary scheme
morphism preserves K-injective cochain complexes of abelian sheaves. -/
@[stacks 0758] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.relocalization_preservesKInjective :
    ∀ {S T : Scheme.{u}} (f : T ⟶ S)
      [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
      [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
      (I : CochainComplex
        (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}) ℤ)
      [I.IsKInjective],
      CochainComplex.IsKInjective
        ((((AlgebraicGeometry.Scheme.Etale.SmallToBig.relocalizationFunctor f).sheafPushforwardContinuous
            AddCommGrpCat.{u} T.smallEtaleTopology
            (S.overGrothendieckTopology @Etale)).mapHomologicalComplex (up ℤ)).obj I))

/- Lemma 59.99.1 (4): restriction from the big étale site to `Sₑₜ` preserves K-injective
cochain complexes of abelian sheaves. -/
@[stacks 0758] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.relocalization_restriction_preservesKInjective :
    ∀ (S : Scheme.{u})
      [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
      [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
      (I : CochainComplex
        (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}) ℤ)
      [I.IsKInjective],
      CochainComplex.IsKInjective
        ((((AlgebraicGeometry.Scheme.Etale.SmallToBig.relocalizationFunctor (𝟙 S)).sheafPushforwardContinuous
            AddCommGrpCat.{u} S.smallEtaleTopology
            (S.overGrothendieckTopology @Etale)).mapHomologicalComplex (up ℤ)).obj I))

/- The scalar-extension adjunction used by the `Spec ℤ` module counterexample. -/
#check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.Module.specIntegerRestrictionScalars_rightAdjoint :
    (SheafOfModules.restrictScalars
      (AlgebraicGeometry.Scheme.Etale.SmallToBig.ringedToposHom
        (𝟙 (Spec (CommRingCat.of ℤ)))).structureMap).IsRightAdjoint)

/- Lemma 59.99.1 (5): for `S = Spec ℤ`, restriction from the big étale ringed topos to `Sₑₜ`
does not preserve injective module sheaves. -/
@[stacks 0758] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.Module.specIntegerModulePullback_not_preservesInjective :
    ¬ AlgebraicGeometry.Scheme.Etale.SmallToBig.Module.specIntegerModulePullback.PreservesInjectiveObjects)

end

end
