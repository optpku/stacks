module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.LocalizedChern.ClosedCover.Additive

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/- Lemma 42.47.9: the localized Newton class of a binary biproduct of perfect derived
modules that vanish on the intersection of a set-theoretic closed cover is the sum of
their localized Newton classes. -/
@[stacks 0FAM] #check (AlgebraicGeometry.LocalizedChern.localizedNewtonClass_biprod :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {delta : S → ℤ}
    [IsDimensionFunction delta] {X : Over S} [LocallyOfFiniteType X.hom]
    {X₁ X₂ : Scheme.{u}} (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (E₂ F₂ : RingedSpace.ModuleDerived X₂.toRingedSpace)
    (perfectE : RingedSpace.ModuleDerived.IsPerfect E₂)
    (perfectF : RingedSpace.ModuleDerived.IsPerfect F₂)
    (definedE : ChernClass.Derived.IsDefined E₂)
    (definedF : ChernClass.Derived.IsDefined F₂)
    (restrictionZeroE : IsZero
      ((RingedSpace.modulePullbackDerived (pullback.snd i₁ i₂).toShHom).obj E₂))
    (restrictionZeroF : IsZero
      ((RingedSpace.modulePullbackDerived (pullback.snd i₁ i₂).toShHom).obj F₂))
    (classes : ChernClass.Theory delta X.hom) (p : ℕ)
    (localizedE localizedF localizedBiprod : BivariantClass delta
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) (p : ℤ))
    (hlocalizedE : BivariantClass.IsLocalizedExtension delta X i₁ i₂ (p : ℤ)
      (ChernClass.Derived.newtonClass delta (i₂ ≫ X.hom)
        (classes.reanchor (Over.mk (i₂ ≫ X.hom))) E₂ perfectE definedE p) localizedE)
    (hlocalizedF : BivariantClass.IsLocalizedExtension delta X i₁ i₂ (p : ℤ)
      (ChernClass.Derived.newtonClass delta (i₂ ≫ X.hom)
        (classes.reanchor (Over.mk (i₂ ≫ X.hom))) F₂ perfectF definedF p) localizedF)
    (hlocalizedBiprod : BivariantClass.IsLocalizedExtension delta X i₁ i₂ (p : ℤ)
      (ChernClass.Derived.newtonClass delta (i₂ ≫ X.hom)
        (classes.reanchor (Over.mk (i₂ ≫ X.hom))) (E₂ ⊞ F₂)
        (perfectE.biprod perfectF) (definedE.biprod definedF) p) localizedBiprod),
    localizedBiprod = BivariantClass.pointwiseAdd delta
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) (p : ℤ) localizedE localizedF)

end AlgebraicGeometry.LocalizedChern
