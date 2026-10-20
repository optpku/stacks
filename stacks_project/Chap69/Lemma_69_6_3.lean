/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AlternatingCech.Cohomology
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open HomologicalComplex HomologicalComplex₂ Opposite ComplexShape

open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 69.6.3: A surjective étale morphism of algebraic spaces gives a canonical
comparison from the alternating Čech complex to derived global sections. Its Ext
spectral sequence converges to sheaf cohomology. -/
@[stacks 0725] #check (AlgebraicGeometry.AlgebraicSpace.alternatingCechToRGamma :
  ∀ {S : Scheme.{u}} {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F]
    [HasDerivedCategory AddCommGrpCat.{u + 1}],
    DerivedCategory.Q.obj ((alternatingCechComplex f F).extend embeddingUpNat) ⟶
      DerivedCategory.Q.obj (injectiveGammaComplex F))

#check (AlgebraicGeometry.AlgebraicSpace.alternatingCechSpectralSequence :
  ∀ {S : Scheme.{u}} {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F],
    CohomologicalSpectralSequenceNat AddCommGrpCat.{u + 1} 1)

#check (AlgebraicGeometry.AlgebraicSpace.alternatingCechSpectralSequence_pageOne_ext :
  ∀ {S : Scheme.{u}} {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F]
    (p q : ℕ),
    IsIsomorphic (((alternatingCechSpectralSequence f F).page 1 le_rfl).X (p, q))
      (AddCommGrpCat.of (Abelian.Ext ((koszulComplex f).X p) F q)))

#check (AlgebraicGeometry.AlgebraicSpace.alternatingCechSpectralSequence_convergesTo :
  ∀ {S : Scheme.{u}} {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Surjective f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F],
    CohomologicalSpectralSequenceNat.ConvergesTo (alternatingCechSpectralSequence f F)
      (fun n ↦ (Sheaf.functorH (smallEtaleTopology X) n).obj F))

