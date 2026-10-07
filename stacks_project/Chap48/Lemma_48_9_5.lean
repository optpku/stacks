module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.ClosedImmersion.InternalHom
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 48.9.5 (1): for a pseudo-coherent closed immersion, derived internal Hom from
   the structure sheaf of the source preserves bounded-below quasicoherent cohomology. -/
@[stacks 0A78] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.closedImmersionInternalHomPlus :
    ∀ {X Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X)
      [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.PseudoCoherent i],
      AlgebraicGeometry.Scheme.DerivedQCoh.Plus X ⥤
        AlgebraicGeometry.Scheme.DerivedQCoh.Plus Z)

/- Lemma 48.9.5 (2): on affine spectra, derived coextension of scalars and
   closed-immersion internal Hom agree under affine derived sheafification. -/
@[stacks 0A78] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.affineInternalHomPlus_square_isomorphic :
    ∀ {A B : CommRingCat.{u}} (f : A ⟶ B)
      [AlgebraicGeometry.IsClosedImmersion (AlgebraicGeometry.Spec.map f)]
      [AlgebraicGeometry.PseudoCoherent (AlgebraicGeometry.Spec.map f)],
      IsIsomorphic
        (AlgebraicGeometry.Scheme.DerivedQCoh.derivedCoextensionPlus f ⋙
          AlgebraicGeometry.Scheme.DerivedQCoh.affineTildePlus B)
        (AlgebraicGeometry.Scheme.DerivedQCoh.affineTildePlus A ⋙
          AlgebraicGeometry.Scheme.DerivedQCoh.closedImmersionInternalHomPlus
            (AlgebraicGeometry.Spec.map f)))

/- A closed immersion into a locally Noetherian scheme has the pseudo-coherence required
   in the first clause. -/
#check (AlgebraicGeometry.PseudoCoherent.closedImmersion_of_isLocallyNoetherian :
  ∀ {X Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X)
    [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsClosedImmersion i],
    AlgebraicGeometry.PseudoCoherent i)
