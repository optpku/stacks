module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.KernelPairCoequalizer
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.KernelPairCoequalizer

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/- Lemma 81.13.1
The kernel pair of a proper morphism with locally Noetherian target has a
coequalizer among all algebraic spaces over the arbitrary base scheme `S`.
-/
@[stacks 0AGG] #check
  (AlgebraicGeometry.AlgebraicSpace.KernelPairCoequalizer.isCoequalizer :
    ∀ (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g]
      {Z : AlgebraicSpace S} (φ : Y ⟶ Z),
      fst g ≫ φ = snd g ≫ φ → ∃! ψ : space g ⟶ Z, fromSource g ≫ ψ = φ)

#check (AlgebraicGeometry.AlgebraicSpace.KernelPairCoequalizer.instIsFinite_toTarget :
  ∀ (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g], IsFinite (toTarget g))

#check (AlgebraicGeometry.AlgebraicSpace.KernelPairCoequalizer.instProper_fromSource :
  ∀ (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g], Proper (fromSource g))

#check (AlgebraicGeometry.AlgebraicSpace.KernelPairCoequalizer.instSurjective_fromSource :
  ∀ (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g], Surjective (fromSource g))

#check
  (AlgebraicGeometry.AlgebraicSpace.KernelPairCoequalizer.instUniversallyInjective_toTarget :
    ∀ (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g], UniversallyInjective (toTarget g))

#check
  (AlgebraicGeometry.AlgebraicSpace.KernelPairCoequalizer.instUniversalHomeomorphism_toTarget :
    ∀ (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g] [Surjective g],
      UniversalHomeomorphism (toTarget g))

#check (AlgebraicGeometry.AlgebraicSpace.KernelPairCoequalizer.fromSource_comp_toTarget :
  ∀ (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g], fromSource g ≫ toTarget g = g)

#check (AlgebraicGeometry.AlgebraicSpace.KernelPairCoequalizer.equalizes :
  ∀ (g : Y ⟶ X) [IsLocallyNoetherian X] [Proper g],
    fst g ≫ fromSource g = snd g ≫ fromSource g)
