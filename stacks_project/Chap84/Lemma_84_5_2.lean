module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Injective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Injective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Relocalization
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open AlgebraicGeometry.Scheme.Etale.SmallToBig.Module
open ComplexShape

noncomputable section

universe u

/- Lemma 84.5.2 (1): inverse image from `(Spaces/X)_étale` to `Y_étale` along an
arbitrary morphism of algebraic spaces over `S` preserves injective abelian sheaves. -/
@[stacks 0DG8] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig.relocalization_preservesInjective :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
      [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
      [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
      (I : Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})
      [Injective I],
      Injective ((inverseImage f).obj I))

/- Lemma 84.5.2 (2): restriction from `(Spaces/X)_étale` to `X_étale` preserves
injective abelian sheaves. -/
@[stacks 0DG8] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig.relocalization_restriction_preservesInjective :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
      [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
      (I : Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})
      [Injective I],
      Injective ((inverseImage (𝟙 X)).obj I))

/- Lemma 84.5.2 (3): inverse image from `(Spaces/X)_étale` to `Y_étale` along an
arbitrary morphism of algebraic spaces over `S` preserves K-injective cochain
complexes of abelian sheaves. -/
@[stacks 0DG8] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig.relocalization_preservesKInjective :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
      [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
      [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
      (I : CochainComplex (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1}) ℤ)
      [I.IsKInjective],
      CochainComplex.IsKInjective
        (((inverseImage f).mapHomologicalComplex (up ℤ)).obj I))

/- Lemma 84.5.2 (4): restriction from `(Spaces/X)_étale` to `X_étale` preserves
K-injective cochain complexes of abelian sheaves. -/
@[stacks 0DG8] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig.relocalization_restriction_preservesKInjective :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
      [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
      (I : CochainComplex (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1}) ℤ)
      [I.IsKInjective],
      CochainComplex.IsKInjective
        (((inverseImage (𝟙 X)).mapHomologicalComplex (up ℤ)).obj I))

/- Lemma 84.5.2 (5): the corresponding statements for modules do not hold. -/
@[stacks 0DG8] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.Module.specIntegerModulePullback_not_preservesInjective :
    ¬ specIntegerModulePullback.PreservesInjectiveObjects)

end
