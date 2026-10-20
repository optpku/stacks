module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.LocalizedChern.Compactification.Additive

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/- Lemma 42.49.8: for two perfect derived objects on the same proper compactification,
with defined Chern classes and zero restrictions to the specified closed part of infinity,
the canonical localized Newton class on Z → X of their binary biproduct is the sum of
their canonical localized Newton classes in every natural degree. -/
@[stacks 0FAZ] #check
  (AlgebraicGeometry.LocalizedChern.newtonClassAtZero_biprod :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] {delta : S → ℤ} [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z W T : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (b : W ⟶ ProjectiveLineFamily.space X) [IsProper b]
    [IsIso (b ∣_ BivariantClass.GysinAtInfinity.affinePart X)]
    (Q Q' : RingedSpace.ModuleDerived W.toRingedSpace)
    (perfectQ : RingedSpace.ModuleDerived.IsPerfect Q)
    (perfectQ' : RingedSpace.ModuleDerived.IsPerfect Q')
    (definedQ : ChernClass.Derived.IsDefined Q)
    (definedQ' : ChernClass.Derived.IsDefined Q')
    (t : T ⟶ (BivariantClass.GysinAtInfinity.infinityFiber X b).left)
    [IsClosedImmersion t]
    (containsComplement :
      (BivariantClass.GysinAtInfinity.infinityToX X b).left.base ⁻¹'
          (Set.range i.base)ᶜ ⊆ Set.range t.base)
    (p : ℕ)
    (restrictionZeroQ : IsZero
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q))
    (restrictionZeroQ' : IsZero
      ((RingedSpace.modulePullbackDerived
        (t ≫ (BivariantClass.GysinAtInfinity.infinityInclusion X b).left).toShHom).obj Q'))
    (classes : ChernClass.Theory delta
      (BivariantClass.GysinAtInfinity.compactification X b).hom)
    (outputQ outputQ' outputBiprod : BivariantClass delta
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ))
    (houtputQ : IsCompactificationLocalization delta i b t (p : ℤ)
      (EnvelopeCaps.derivedClass delta classes Q perfectQ definedQ false p) outputQ)
    (houtputQ' : IsCompactificationLocalization delta i b t (p : ℤ)
      (EnvelopeCaps.derivedClass delta classes Q' perfectQ' definedQ' false p) outputQ')
    (houtputBiprod : IsCompactificationLocalization delta i b t (p : ℤ)
      (EnvelopeCaps.derivedClass delta classes (Q ⊞ Q')
        (perfectQ.biprod perfectQ') (definedQ.biprod definedQ') false p) outputBiprod),
    outputBiprod = BivariantClass.pointwiseAdd delta
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ) outputQ outputQ')

end AlgebraicGeometry.LocalizedChern
