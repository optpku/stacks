module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AlternatingCech.CharacterTwist
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 69.6.6. The alternating Čech spectral sequence has first page given
by sign-twisted cohomology of the off-diagonal quotients and converges to
étale cohomology of the base. -/
@[stacks 0728] #check (AlgebraicGeometry.AlgebraicSpace.alternatingCechSpectralSequence_pageOne_characterTwist :
  ∀ {S : Scheme.{u}} {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f] [Surjective f] [Separated f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] (p : ℕ) {Up : AlgebraicSpace S}
    (q : offDiagonal f (p + 1) ⟶ Up)
    [IsFreeQuotient (offDiagonalPermLift f (p + 1)) q] (π : Up ⟶ X) [Etale π]
    (h_toBase : q ≫ π = offDiagonalToBase f (p + 1))
    [HasSheafify (smallEtaleTopology Up) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (smallEtaleTopology Up) AddCommGrpCat.{u + 1})]
    (n : ℕ),
    IsIsomorphic (((alternatingCechSpectralSequence f F).page 1 le_rfl).X (p, n))
      ((Sheaf.functorH (smallEtaleTopology Up) n).obj
        (offDiagonalCharacterTwist f F p q π)))

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
