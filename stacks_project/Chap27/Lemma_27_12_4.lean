/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.MorphismDatum
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {T : Scheme.{u}}
variable (tau tau' : Proj.MorphismDatum 𝒜 T)
variable {phi phi' : T ⟶ Proj 𝒜}
variable (hphi : Proj.MorphismDatum.AssociatedTo 𝒜 tau phi)
variable (hphi' : Proj.MorphismDatum.AssociatedTo 𝒜 tau' phi')

/- Lemma 27.12.4: compatibility at the least common multiple, equivalence at the product,
compatibility at some positive common multiple, and equality of the associated morphisms are
equivalent. -/
@[stacks 01NB] #check
  (AlgebraicGeometry.Proj.MorphismDatum.equivalent_tfae 𝒜 tau tau' hphi hphi' :
    List.TFAE [
      Proj.MorphismDatum.CompatibleAtLcm 𝒜 tau tau',
      Proj.MorphismDatum.Equivalent 𝒜 tau tau',
      Proj.MorphismDatum.SomeCommonMultipleCompatible 𝒜 tau tau',
      phi = phi'
    ])

end AlgebraicGeometry
