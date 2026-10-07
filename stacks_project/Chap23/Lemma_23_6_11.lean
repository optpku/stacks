module

public import ReasLib.RingTheory.DividedPowers.Tate
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u w

section Lifting

variable {R : Type u} [CommRing R]
variable {A B : DividedPowerChainAlgebra R}
variable {generators : ℕ → Type w}
variable (P : DividedPowerGradedAlgebra.FreePresentation A.toGradedAlgebra generators)
variable (hB : B.toChainDGAlgebra.PositiveHomologyVanishes)
variable (f0 : A.toChainDGAlgebra.homologyZero →ₐ[R] B.toChainDGAlgebra.homologyZero)

/- Lemma 23.6.11 (Tag 09PP): a map on zeroth homology lifts from a freely presented
divided-power chain DGA to any compatible target with vanishing positive homology. -/
@[stacks 09PP]
#check (DividedPowerGradedAlgebra.FreePresentation.existsHom_liftingH0 P hB f0 :
  ∃ f : A ⟶ B, f.InducesH0 f0)

end Lifting

/- Tate-resolution comparisons use the general morphism owner, specialized to the identity target
map. Identity, composition, forgetting to augmented chain DGAs, and existence are separate APIs. -/
#check @TateResolution.Hom
#check @TateResolution.Hom.id
#check @TateResolution.Hom.comp
#check @TateResolution.Hom.toAugmentationHom
#check @TateResolution.Hom.id_toAugmentationHom
#check @TateResolution.Hom.comp_toAugmentationHom
#check @TateResolution.Hom.nonempty
#check @TateResolution.Hom.nonempty_over_id
