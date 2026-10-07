module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import ReasLib.RingTheory.Ideal.FiniteGeneration.Family
public import ReasLib.AlgebraicGeometry.Scheme.Spectrum.OpenComplement

/-!
# Affine ideal-complement section primitives

Sections of tilde modules over the affine open `Spec A ∖ V(I)` and basic-open
fraction sections give the section maps used in ideal-power comparisons.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry PrimeSpectrum
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {A : Type u} [CommRing A]

/-- The presheaf underlying the canonical sheaf associated to `AlgebraicGeometry.tilde M` on
`Spec A`. -/
abbrev tildePresheaf (M : ModuleCat A) :=
  (AlgebraicGeometry.modulesSpecToSheaf.obj
    (AlgebraicGeometry.tilde (R := CommRingCat.of A) M)).presheaf

/-- The canonical sheaf associated to `AlgebraicGeometry.tilde M` on `Spec A`. -/
noncomputable abbrev tildeSheaf (M : ModuleCat A) :
    TopCat.Sheaf (ModuleCat A) (Spec (.of A)) :=
  AlgebraicGeometry.modulesSpecToSheaf.obj
    (AlgebraicGeometry.tilde (R := CommRingCat.of A) M)

/-- The open complement `Spec A ∖ V(I)`. -/
abbrev idealComplementOpens (I : Ideal A) : (Spec (.of A)).Opens :=
  Scheme.idealComplementOpens I

/-- The `A`-module of sections of `tilde M` on `Spec A ∖ V(I)`. -/
noncomputable abbrev idealComplementTildeSections (I : Ideal A) (M : ModuleCat A) :
    ModuleCat A :=
  (tildePresheaf M).obj (Opposite.op (idealComplementOpens I))

/-- The raw map on complement sections induced by a module morphism. -/
noncomputable def idealComplementTildeSectionsMapRaw (I : Ideal A)
    {M N : ModuleCat A} (f : M ⟶ N) :
    idealComplementTildeSections I M ⟶ idealComplementTildeSections I N :=
  (AlgebraicGeometry.modulesSpecToSheaf.map (AlgebraicGeometry.tilde.map f)).hom.app
    (Opposite.op (idealComplementOpens I))

/-- The raw section map induced by the identity morphism of a module is the identity. -/
theorem idealComplementTildeSectionsMapRaw_id (I : Ideal A) (M : ModuleCat A) :
    idealComplementTildeSectionsMapRaw I (𝟙 M) =
      𝟙 (idealComplementTildeSections I M) := sorry

/-- Raw section maps induced by composable module morphisms respect composition. -/
theorem idealComplementTildeSectionsMapRaw_comp (I : Ideal A)
    {M N P : ModuleCat A} (f : M ⟶ N) (g : N ⟶ P) :
    idealComplementTildeSectionsMapRaw I (f ≫ g) =
      idealComplementTildeSectionsMapRaw I f ≫
        idealComplementTildeSectionsMapRaw I g := sorry

/-- Sections of associated tilde modules over `Spec A ∖ V(I)`, assembled as a functor whose map
is the map of associated sheaves evaluated on the complement. -/
noncomputable def idealComplementTildeSectionsFunctor (I : Ideal A) :
    ModuleCat A ⥤ ModuleCat A where
  obj M := idealComplementTildeSections I M
  map f := idealComplementTildeSectionsMapRaw I f
  map_id M := idealComplementTildeSectionsMapRaw_id I M
  map_comp f g := idealComplementTildeSectionsMapRaw_comp I f g

/-- The section map induced by a morphism of tilde modules, obtained from the canonical section
functor. -/
noncomputable abbrev idealComplementTildeSectionsMap (I : Ideal A) {M N : ModuleCat A}
    (f : M ⟶ N) :
    idealComplementTildeSections I M ⟶ idealComplementTildeSections I N :=
  (idealComplementTildeSectionsFunctor I).map f

/-- The standard localization-to-basic-open equivalence before specializing a raw ring carrier. -/
noncomputable abbrev tildeBasicOpenIsoOfCommRingCat {R : CommRingCat.{u}}
    (M : ModuleCat R) (f : R) :
    LocalizedModule.Away f M ≃ₗ[R]
      ((AlgebraicGeometry.modulesSpecToSheaf.obj (AlgebraicGeometry.tilde M)).presheaf.obj
        (Opposite.op (PrimeSpectrum.basicOpen f)) : Type u) :=
  IsLocalizedModule.iso (.powers f) (AlgebraicGeometry.tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom

/-- The standard localization-to-basic-open equivalence for a tilde module. -/
noncomputable abbrev tildeBasicOpenIso (M : ModuleCat A) (f : A) :
    LocalizedModule.Away f M ≃ₗ[A]
      ((tildePresheaf M).obj (Opposite.op (PrimeSpectrum.basicOpen f)) : Type u) :=
  tildeBasicOpenIsoOfCommRingCat (R := CommRingCat.of A) M f

/-- The section on `D(f)` represented by the fraction `x / f^n` in `tilde M`. -/
noncomputable def tildeBasicOpenPowerSection (M : ModuleCat A) (f : A) (n : ℕ) (x : M) :
    ((tildePresheaf M).obj (Opposite.op (PrimeSpectrum.basicOpen f)) : Type u) :=
  tildeBasicOpenIso M f
    (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap (Submonoid.powers f) M) x
      (⟨f ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f))

/-- Fractions with denominator `f^n` agree when their numerators differ by an element killed by
`f^n`.  This is the representative-independence bridge used by quotient-Hom comparison maps. -/
theorem tildeBasicOpenPowerSection_eq_of_smul_pow_eq_zero
    (M : ModuleCat A) (f : A) (n : ℕ) {x y : M}
    (h : f ^ n • (x - y) = 0) :
    tildeBasicOpenPowerSection M f n x = tildeBasicOpenPowerSection M f n y := sorry

end AlgebraicGeometry.Scheme.Modules
