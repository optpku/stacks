module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Cohomology
public import stacks_project.Chap36.Lemma_36_10_1_PseudoCoherent
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 36.10.1 (1): above the cutoff, the cohomology sheaves of an
`m`-pseudo-coherent derived `𝒪_X`-module on a scheme are quasi-coherent. -/
@[stacks 08E5] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.PseudoCoherent.higherCohomology_isQuasicoherent :
    ∀ {X : AlgebraicGeometry.Scheme.{u}}
      {E : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace} {m i : ℤ},
      AlgebraicGeometry.Scheme.IsMPseudoCoherent X E m →
        m < i →
          (AlgebraicGeometry.RingedSpace.ModuleDerived.cohomologySheaf E i).IsQuasicoherent)

/- Lemma 36.10.1 (2): the degree-`m` cohomology sheaf of an `m`-pseudo-coherent
derived `𝒪_X`-module on a scheme is a quotient of a quasi-coherent module. -/
@[stacks 08E5] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.PseudoCoherent.exists_quasicoherent_epi :
    ∀ {X : AlgebraicGeometry.Scheme.{u}}
      {E : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace} {m : ℤ},
      AlgebraicGeometry.Scheme.IsMPseudoCoherent X E m →
        ∃ F : AlgebraicGeometry.RingedSpace.QCoh X.toRingedSpace,
          ∃ f : F.obj ⟶ AlgebraicGeometry.RingedSpace.ModuleDerived.cohomologySheaf E m,
            Epi f)

/- Lemma 36.10.1 (3): a pseudo-coherent derived `𝒪_X`-module on a scheme has
quasi-coherent cohomology in every degree. -/
@[stacks 08E5] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.PseudoCoherent.derivedQuasiCoherentModuleProperty :
    ∀ {X : AlgebraicGeometry.Scheme.{u}}
      {E : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace},
      AlgebraicGeometry.Scheme.IsPseudoCoherent X E →
        AlgebraicGeometry.Scheme.derivedQuasiCoherentModuleProperty X E)
