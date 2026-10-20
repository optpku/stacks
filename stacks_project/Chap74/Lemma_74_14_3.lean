module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocal.LocalAtSource
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

/- Lemma 74.14.3 (1): if a property of morphisms of schemes is étale local on the
source-and-target and fpqc local on the source, then the corresponding property
of morphisms of algebraic spaces is fpqc local on the source. -/
@[stacks 06ER] #check
  (AlgebraicGeometry.AlgebraicSpace.etaleLocal_isLocalAtSource_fpqc :
    ∀ {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
      [IsEtaleLocalAtSourceAndTarget P]
      [P.IsLocalAtSource Scheme.fpqcPrecoverage],
      (etaleLocal P).IsLocalAtSource (fpqcPrecoverage S))

/- Lemma 74.14.3 (2): if a property of morphisms of schemes is étale local on the
source-and-target and fppf local on the source, then the corresponding property
of morphisms of algebraic spaces is fppf local on the source. -/
@[stacks 06ER] #check
  (AlgebraicGeometry.AlgebraicSpace.etaleLocal_isLocalAtSource_fppf :
    ∀ {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
      [IsEtaleLocalAtSourceAndTarget P]
      [P.IsLocalAtSource Scheme.fppfPrecoverage],
      (etaleLocal P).IsLocalAtSource (fppfPrecoverage S))

/- Lemma 74.14.3 (3): if a property of morphisms of schemes is étale local on the
source-and-target and syntomic local on the source, then the corresponding
property of morphisms of algebraic spaces is syntomic local on the source. -/
@[stacks 06ER] #check
  (AlgebraicGeometry.AlgebraicSpace.etaleLocal_isLocalAtSource_syntomic :
    ∀ {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
      [IsEtaleLocalAtSourceAndTarget P]
      [P.IsLocalAtSource Scheme.bigSyntomicPrecoverage],
      (etaleLocal P).IsLocalAtSource (precoverage (@Syntomic S)))

/- Lemma 74.14.3 (4): if a property of morphisms of schemes is étale local on the
source-and-target and smooth local on the source, then the corresponding
property of morphisms of algebraic spaces is smooth local on the source. -/
@[stacks 06ER] #check
  (AlgebraicGeometry.AlgebraicSpace.etaleLocal_isLocalAtSource_smooth :
    ∀ {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
      [IsEtaleLocalAtSourceAndTarget P]
      [P.IsLocalAtSource Scheme.bigSmoothPrecoverage],
      (etaleLocal P).IsLocalAtSource (precoverage (@Smooth S)))

/- Lemma 74.14.3 (5): if a property of morphisms of schemes is étale local on the
source-and-target and étale local on the source, then the corresponding
property of morphisms of algebraic spaces is étale local on the source. -/
@[stacks 06ER] #check
  (AlgebraicGeometry.AlgebraicSpace.etaleLocal_isLocalAtSource_etale :
    ∀ {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
      [IsEtaleLocalAtSourceAndTarget P]
      [P.IsLocalAtSource Scheme.etalePrecoverage],
      (etaleLocal P).IsLocalAtSource (@etalePrecoverage S))
