module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Hilbert.Quot

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

/- Lemma 99.9.2: in Situation 99.9.1, the Hilbert functor Hilb_{X/B} equals the
Quot functor Quot_{𝒪_X/X/B} as functors (Sch/B)ᵒᵖ ⥤ Sets. The identification
sends a closed subspace Z ⊂ X_T with Z ⟶ T of finite presentation, flat, and
proper to the quotient 𝒪_{X_T} ⟶ ι_* 𝒪_Z, and conversely cuts out Z from
I = Ker(𝒪_{X_T} ⟶ Q). -/
@[stacks 0D00] #check (AlgebraicGeometry.AlgebraicSpace.Hilbert.quotIso :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f],
    Hilbert.hilbert f ≅ Quot.quot f (SheafOfModules.unit (structureSheaf X)))
