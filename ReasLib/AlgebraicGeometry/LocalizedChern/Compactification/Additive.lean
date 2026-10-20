module

public import ReasLib.AlgebraicGeometry.LocalizedChern.Compactification
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.Biproduct

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- The compactification-localized Newton class of the binary biproduct of two perfect
derived modules with defined Chern classes, both vanishing on the specified part of
infinity, is the pointwise sum of their compactification-localized Newton classes. -/
theorem newtonClassAtZero_biprod
    {S : Scheme.{u}} [UniversallyCatenary S] {delta : S → ℤ} [IsDimensionFunction delta]
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
        (perfectQ.biprod perfectQ') (definedQ.biprod definedQ') false p) outputBiprod) :
    outputBiprod = BivariantClass.pointwiseAdd delta
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ) outputQ outputQ' := sorry

end AlgebraicGeometry.LocalizedChern
