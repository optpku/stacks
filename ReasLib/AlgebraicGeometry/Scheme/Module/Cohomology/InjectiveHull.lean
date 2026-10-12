/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.Algebra.Module.Injective.Hull
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.RingTheory.RegularLocalRing.Defs

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a regular local ring containing a field, an étale quasi-compact morphism avoiding
the closed point and affine over the punctured spectrum has positive-degree structure-sheaf
cohomology isomorphic to a direct sum of copies of any injective hull of the residue field. -/
theorem cohomology_isDirectSum_injectiveHull
    {k A : Type u} [Field k] [CommRing A] [Algebra k A] [IsRegularLocalRing A]
    {V : Scheme.{u}} (f : V ⟶ Spec (CommRingCat.of A)) [Etale f] [QuasiCompact f]
    (h_m : IsLocalRing.closedPoint A ∉ Set.range f)
    (g : V ⟶ PuncturedSpectrum.scheme A) [IsAffineHom g]
    (h_factor : g ≫ (PuncturedSpectrum.puncturedOpen A).ι = f)
    {E : Type u} [AddCommGroup E] [Module A E] [Module.Injective A E]
    (ιE : IsLocalRing.ResidueField A →ₗ[A] E) (hι : ιE.IsInjectiveHull) :
    ∀ i : ℕ, 0 < i →
      ∃ J : Type u,
        Nonempty
          (Scheme.Hom.cohomology f (SheafOfModules.unit V.ringCatSheaf : V.Modules) i ≅
            ModuleCat.of A (DirectSum J (fun _ ↦ E))) := sorry

end AlgebraicGeometry.Scheme.Hom
