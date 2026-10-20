module

public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissage.FreePresentation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

variable {S : Scheme.{u}} {X : Over S} {F : X.left.Modules}
  [LocallyOfFiniteType X.hom] [F.IsQuasicoherent] [F.IsFiniteType] {s : S}

/- Lemma 38.4.9 (1): At the generic point of the model fibre, the pushforward
of the auxiliary module admits a finite free map of positive rank whose induced
fibre map is bijective. -/
@[stacks 05HF] #check
  (AlgebraicGeometry.Scheme.Modules.OneStepDevissage.existsFreeMapFiberBijective :
    ∀ (D : AlgebraicGeometry.Scheme.Modules.OneStepDevissage X F s)
      (ξ : Scheme.Hom.fiber D.Y.hom s),
      IsGenericPoint ξ (Set.univ : Set (Scheme.Hom.fiber D.Y.hom s)) →
        ∃ (r : ℕ) (_ : 0 < r)
          (α : (SheafOfModules.freeFin r : Scheme.Modules D.Y.left) ⟶
            (Scheme.Modules.pushforward D.π.left).obj D.G),
          Function.Bijective
            (Scheme.Modules.fiberMap
              ((Scheme.Modules.pullback (Scheme.Hom.fiberι D.Y.hom s)).map α) ξ))

/- Lemma 38.4.9 (2): Every positive-rank finite free map that is bijective at
the generic fibre point has cokernel of strictly smaller fibrewise support
dimension than the original module. -/
@[stacks 05HF] #check
  (AlgebraicGeometry.Scheme.Modules.OneStepDevissage.cokernelFiberSupportDimensionLt :
    ∀ (D : AlgebraicGeometry.Scheme.Modules.OneStepDevissage X F s)
      (ξ : Scheme.Hom.fiber D.Y.hom s),
      IsGenericPoint ξ (Set.univ : Set (Scheme.Hom.fiber D.Y.hom s)) →
      ∀ (r : ℕ), 0 < r →
      ∀ (α : (SheafOfModules.freeFin r : Scheme.Modules D.Y.left) ⟶
        (Scheme.Modules.pushforward D.π.left).obj D.G),
      Function.Bijective
          (Scheme.Modules.fiberMap
            ((Scheme.Modules.pullback (Scheme.Hom.fiberι D.Y.hom s)).map α) ξ) →
        AlgebraicGeometry.Scheme.Modules.fiberSupportDimension
            D.Y.hom (cokernel α) s <
          AlgebraicGeometry.Scheme.Modules.fiberSupportDimension X.hom F s)
