module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.LocalCohomology.EssentiallyConstant

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 52.5.3: if the local cohomology of a finite module over a Noetherian local ring is
isomorphic through the induced comparison to the inverse limit of the local cohomology of a
sequential system of finite modules, then the induced cone is essentially constant. -/
@[stacks 0EHB] #check (localCohomology.inverseSystemCone_isEssentiallyConstant :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (N : SequentialInverseSystem (FGModuleCat.{u} A))
    (f : M ⟶ limit (N ⋙ (ModuleCat.isFG A).ι)) (i : ℕ)
    [IsIso (localCohomology.limitComparison A M N f i)],
    (localCohomology.inverseSystemCone A M N f i).IsEssentiallyConstant)
