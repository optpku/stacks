/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.ClosedImmersion.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Immersion

/-!
# Closed immersions into schemes

This layer recognizes the source of a locally ringed-space closed immersion
into a scheme as a scheme and records quasi-coherence of its kernel ideal.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.IsClosedImmersion

variable {X : Scheme.{u}} {Z : LocallyRingedSpace.{u}}

/-- Around every source point of a closed immersion into a scheme there is an affine scheme
mapping by an open immersion onto a neighbourhood of that point. -/
@[stacks 01IN "affine neighbourhood of a closed subspace"]
theorem exists_affine_openImmersion
    (i : Z ⟶ X.toLocallyRingedSpace) [IsClosedImmersion i] (z : Z) :
    ∃ (R : CommRingCat.{u}) (f : (Spec R).toLocallyRingedSpace ⟶ Z),
      z ∈ Set.range f.base ∧ IsOpenImmersion f := sorry

namespace Source

/-- The source locally ringed space, equipped with its canonical scheme structure induced by a
closed immersion into a scheme. Its underlying locally ringed space is definitionally `Z`. -/
@[stacks 01IN "scheme structure on a closed subspace"]
def scheme (i : Z ⟶ X.toLocallyRingedSpace) [IsClosedImmersion i] : Scheme.{u} :=
  LocallyRingedSpace.IsOpenImmersion.scheme Z (exists_affine_openImmersion i)

/-- The given closed immersion, regarded as a scheme morphism from its canonical source
scheme. -/
@[stacks 01IN "scheme morphism of a closed subspace"]
def hom (i : Z ⟶ X.toLocallyRingedSpace) [IsClosedImmersion i] : scheme i ⟶ X :=
  ⟨i⟩

/-- The canonical scheme morphism carried by a locally ringed-space closed immersion is a closed
immersion. -/
@[stacks 01IN "canonical source scheme map is closed", instance]
theorem hom_isClosedImmersion
    (i : Z ⟶ X.toLocallyRingedSpace) [IsClosedImmersion i] :
    AlgebraicGeometry.IsClosedImmersion (hom i) := sorry

/-- The canonical identification between the underlying locally ringed space of the source
scheme and the original source. -/
@[stacks 01IN "underlying locally ringed space of a closed subspace"]
def iso (i : Z ⟶ X.toLocallyRingedSpace) [IsClosedImmersion i] :
    (scheme i).toLocallyRingedSpace ≅ Z :=
  Iso.refl Z

/-- The canonical source identification factors the induced scheme morphism through the
original closed immersion. -/
@[stacks 01IN "closed subspace source factorization"]
theorem iso_hom_comp (i : Z ⟶ X.toLocallyRingedSpace) [IsClosedImmersion i] :
    (iso i).hom ≫ i = (hom i).toLRSHom := sorry

end Source

/-- The source of a locally ringed-space closed immersion into a scheme admits a compatible
scheme presentation. -/
@[stacks 01IN "closed subspace of a scheme"]
theorem exists_schemeHom
    (i : Z ⟶ X.toLocallyRingedSpace) [IsClosedImmersion i] :
    ∃ (Y : Scheme.{u}) (j : Y ⟶ X) (e : Y.toLocallyRingedSpace ≅ Z),
      e.hom ≫ i = j.toLRSHom ∧ AlgebraicGeometry.IsClosedImmersion j := sorry

end AlgebraicGeometry.LocallyRingedSpace.IsClosedImmersion

namespace AlgebraicGeometry.LocallyRingedSpace.Hom.KernelIdeal

/-- The kernel ideal sheaf of a closed immersion into a scheme is quasi-coherent. -/
@[stacks 01IN "closed immersion kernel is quasi-coherent", instance]
theorem isQuasicoherent
    {X : Scheme.{u}} {Z : LocallyRingedSpace.{u}}
    (i : Z ⟶ X.toLocallyRingedSpace) [IsClosedImmersion i] :
    i.kernelIdealSheaf.IsQuasicoherent := sorry

end AlgebraicGeometry.LocallyRingedSpace.Hom.KernelIdeal
