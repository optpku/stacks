module

public import ReasLib.RingTheory.FormalFiber.Gorenstein
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Lemma 47.23.2: if a Noetherian local ring `A` has a dualizing complex, then every formal
fibre of `A` is a Gorenstein ring. -/
@[stacks 0AWY] #check
  (CategoryTheory.DerivedCategory.IsDualizingComplex.formalFibersGorenstein :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex H),
      FieldAlgebraProperty.HoldsOnFormalFibers
        (fun _ R ↦ IsGorensteinRing R) A)
