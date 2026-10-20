module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Invertible
import StacksCheckRecall

@[expose] public section

/- Lemma 17.25.5 (1): on a ringed space, the tensor product of two invertible
`𝒪_X`-modules is invertible. This is the opens-site specialization of the Chapter 18
owner theorem. -/
@[stacks 01CT "(1)"]
#check @CategoryTheory.MonoidalCategory.isInvertibleObject.tensor

/- Lemma 17.25.5 (2), dual clause: on a ringed space, the internal-Hom dual
`(ihom L).obj (𝟙_ _)` of an invertible `𝒪_X`-module is invertible. This is the same opens-site
specialization. -/
@[stacks 01CT "(2), dual"]
#check @SheafOfModules.RingedSite.dual.isInvertible

/- Lemma 17.25.5 (2), evaluation clause: on a ringed space, the evaluation morphism
`L ⊗ (ihom L).obj (𝟙_ _) ⟶ 𝟙_ _` is an isomorphism for invertible `𝒪_X`-modules. This is again the
opens-site specialization of the Chapter 18 owner theorem. -/
@[stacks 01CT "(2), evaluation"]
#check @SheafOfModules.RingedSite.dual.evaluationIsIso
