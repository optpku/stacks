module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.IdealQuotient
import StacksCheckRecall

universe u v

/- Remark 47.13.5: coextension along `A ⟶ A ⧸ I` is naturally isomorphic to
the functor sending an `A`-module to its submodule annihilated by every element of `I`. -/
@[stacks 0A73] #check (CategoryTheory.ModuleCat.IdealTorsion.natIso.{u, v} :
  ∀ {A : Type u} [CommRing A] (I : Ideal A),
    ModuleCat.coextendScalars.{u, u, max u v} (Ideal.Quotient.mk I) ≅
      CategoryTheory.ModuleCat.IdealTorsion.functor.{u, v} I)
