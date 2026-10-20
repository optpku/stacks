module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AlternatingCech.Cohomology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AlternatingCech.OffDiagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.CharacterTwist

/-!
# Sign-twisted cohomology of off-diagonal quotients

The sign-character twist on a free symmetric-group quotient describes the
first page of the alternating Čech spectral sequence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The sheaf `F|_{U_p} ⊗_ℤ ℤ̲(χ_p)` on `U_p,étale`, for a free quotient
`q : W_p ⟶ U_p` of the off-diagonal permutation action and the structure morphism
`π : U_p ⟶ X`. -/
noncomputable def offDiagonalCharacterTwist {U X Up : AlgebraicSpace S}
    (f : U ⟶ X) [Separated f] (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (p : ℕ) (q : offDiagonal f (p + 1) ⟶ Up)
    [IsFree (offDiagonalPermLift f (p + 1))]
    [IsFreeQuotient (offDiagonalPermLift f (p + 1)) q]
    (π : Up ⟶ X) [Etale π] :
    Sheaf (smallEtaleTopology Up) AddCommGrpCat.{u + 1} :=
  tensorIntegerCharacter (offDiagonalPermLift f (p + 1)) q
    (IntegerCharacter.permutationSign (p + 1))
    ((etaleRestrictionSheaf π AddCommGrpCat.{u + 1}).obj F)

/-- `offDiagonalCharacterTwist` is the integer character twist of the restriction of
`F` along `π`. -/
theorem offDiagonalCharacterTwist_def {U X Up : AlgebraicSpace S}
    (f : U ⟶ X) [Separated f] (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (p : ℕ) (q : offDiagonal f (p + 1) ⟶ Up)
    [IsFree (offDiagonalPermLift f (p + 1))]
    [IsFreeQuotient (offDiagonalPermLift f (p + 1)) q]
    (π : Up ⟶ X) [Etale π] :
    offDiagonalCharacterTwist f F p q π =
      tensorIntegerCharacter (offDiagonalPermLift f (p + 1)) q
        (IntegerCharacter.permutationSign (p + 1))
        ((etaleRestrictionSheaf π AddCommGrpCat.{u + 1}).obj F) :=
  rfl

/-- The first page of the alternating Čech spectral sequence of a surjective
étale separated morphism is the cohomology of the sign-twisted restriction on
a free symmetric-group quotient of the off-diagonal fibre power, whose étale
map to the base is compatible with the off-diagonal projection. -/
theorem alternatingCechSpectralSequence_pageOne_characterTwist
    {U X : AlgebraicSpace S} (f : U ⟶ X) [Etale f] [Surjective f] [Separated f]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolution F] (p : ℕ) {Up : AlgebraicSpace S}
    (q : offDiagonal f (p + 1) ⟶ Up)
    [IsFreeQuotient (offDiagonalPermLift f (p + 1)) q] (π : Up ⟶ X) [Etale π]
    (h_toBase : q ≫ π = offDiagonalToBase f (p + 1))
    [HasSheafify (smallEtaleTopology Up) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (smallEtaleTopology Up) AddCommGrpCat.{u + 1})]
    (n : ℕ) :
    IsIsomorphic (((alternatingCechSpectralSequence f F).page 1 le_rfl).X (p, n))
      ((Sheaf.functorH (smallEtaleTopology Up) n).obj
        (offDiagonalCharacterTwist f F p q π)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
