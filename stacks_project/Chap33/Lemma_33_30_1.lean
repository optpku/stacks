module

public import ReasLib.AlgebraicGeometry.Scheme.Module.GlobalSections.Invertible
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

/- Lemma 33.30.1 (1): global sections of the invertible module are invertible. -/
@[stacks 0CDX]
#check
  (AlgebraicGeometry.Scheme.Modules.GlobalSections.invertible_of_trivial_faithfullyFlat_baseChange :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (L : X.Modules)
      [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
      [Scheme.Modules.Invertible L]
      (hff : (algebraMap A B).FaithfullyFlat)
      (htriv : RingedSpace.IsTrivial (Scheme.Modules.AffineBaseChange.baseChange A B f L)),
      Module.Invertible (Γ(X, ⊤)) Γ(L, ⊤))

/- Lemma 33.30.1 (2): global sections of the internal-Hom inverse are invertible. -/
@[stacks 0CDX]
#check
  (AlgebraicGeometry.Scheme.Modules.GlobalSections.inverse_invertible_of_trivial_faithfullyFlat_baseChange :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (L : X.Modules)
      [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
      [Scheme.Modules.Invertible L]
      (hff : (algebraMap A B).FaithfullyFlat)
      (htriv : RingedSpace.IsTrivial (Scheme.Modules.AffineBaseChange.baseChange A B f L)),
      Module.Invertible (Γ(X, ⊤))
        Γ((ihom L).obj (SheafOfModules.unit X.ringCatSheaf : X.Modules), ⊤))

/- Lemma 33.30.1 (3): the global-sections evaluation pairing is bijective. -/
@[stacks 0CDX]
#check
  (AlgebraicGeometry.Scheme.Modules.GlobalSections.evaluation_bijective_of_trivial_faithfullyFlat_baseChange :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (L : X.Modules)
      [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
      [Scheme.Modules.Invertible L]
      (hff : (algebraMap A B).FaithfullyFlat)
      (htriv : RingedSpace.IsTrivial (Scheme.Modules.AffineBaseChange.baseChange A B f L)),
      Function.Bijective (RingedSpace.GlobalSections.evaluationLinearMap L))
