module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Affine.BoundedBelow
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Affine.Coextension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.Affine.BoundedBelow
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.Noetherian

/-!
# Bounded-below internal Hom for closed immersions

This module constructs the bounded-below internal-Hom functor for a pseudo-coherent closed
immersion and compares it with derived coextension on affine schemes.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- For a pseudo-coherent closed immersion `i : Z ⟶ X`, derived internal Hom from `𝒪_Z`
maps bounded-below complexes with quasicoherent cohomology on `X` to such complexes on `Z`. -/
noncomputable def closedImmersionInternalHomPlus {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [PseudoCoherent i] : Plus X ⥤ Plus Z :=
  derivedInternalHomPlus i ⋙ Functor.inv (affinePushforwardToPushforwardStructurePlus i)

/-- After affine pushforward to `i_*𝒪_Z`, bounded-below closed-immersion internal Hom is
the derived coextension model of internal Hom from `i_*𝒪_Z`. -/
theorem closedImmersionInternalHomPlus_comp_affinePushforward_isomorphic
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [PseudoCoherent i] :
    IsIsomorphic
      (closedImmersionInternalHomPlus i ⋙
        affinePushforwardToPushforwardStructurePlus i)
      (derivedInternalHomPlus i) := sorry

/-- For a pseudo-coherent closed immersion of affine spectra, affine derived sheafification
intertwines derived coextension of scalars with closed-immersion internal Hom. -/
theorem affineInternalHomPlus_square_isomorphic {A B : CommRingCat.{u}} (f : A ⟶ B)
    [IsClosedImmersion (Spec.map f)] [PseudoCoherent (Spec.map f)] :
    IsIsomorphic
      (derivedCoextensionPlus f ⋙ affineTildePlus B)
      (affineTildePlus A ⋙ closedImmersionInternalHomPlus (Spec.map f)) := sorry

/-- For a pseudo-coherent closed immersion into a quasi-compact quasi-separated scheme,
the bounded-below restriction of a right adjoint to derived quasicoherent pushforward is
naturally isomorphic to derived internal Hom from the structure sheaf of the source. -/
theorem rightAdjointPlus_isomorphic_internalHom {X Z : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (i : Z ⟶ X)
    [IsClosedImmersion i] [PseudoCoherent i]
    (a : DerivedQCoh X ⥤ DerivedQCoh Z) (adj : pushforwardCohomologyIn i ⊣ a) :
    IsIsomorphic (rightAdjointPlus i a adj) (closedImmersionInternalHomPlus i) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
