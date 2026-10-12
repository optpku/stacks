/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.ModuleCat.BoundedAbove
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Sections
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.Coefficients
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Cover
public import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleCech

variable {A : Type u} [CommRing A] {X : _root_.AlgebraicGeometry.Scheme.{u}}

/-- The integer-graded, `A`-linear Čech-row functor on modules over
`f⁻¹𝒪_(Spec A)`. -/
abbrev rowOverSpecFunctor (f : X ⟶ Spec (CommRingCat.of A)) {ι : Type u}
    (U : ι → X.Opens) :
    (relativeSpace f.toShHom).Modules ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  RingedSpace.ModuleCech.extended (relativeSpace f.toShHom) U ⋙
    ((RingedSpace.moduleSectionsRestrictionFunctor.{u, u, u}
      (relativeSpaceMap f.toShHom) ⊤).mapHomologicalComplex
      (ComplexShape.up ℤ)) ⋙
    ((ModuleCat.restrictScalars.{u, u, u}
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv).hom).mapHomologicalComplex
      (ComplexShape.up ℤ))

/-- The affine-base Čech-row functor preserves zero morphisms, so it applies canonically to
cochain complexes. -/
instance rowOverSpecFunctor_preservesZeroMorphisms
    (f : X ⟶ Spec (CommRingCat.of A)) {ι : Type u} (U : ι → X.Opens) :
    (rowOverSpecFunctor f U).PreservesZeroMorphisms := sorry

/-- The integer-graded Čech row of a module on `X`, regarded as a complex of `A`-modules
through a morphism `f : X ⟶ Spec A`. -/
abbrev rowOverSpec (f : X ⟶ Spec (CommRingCat.of A)) {ι : Type u}
    (U : ι → X.Opens) (F : X.Modules) : CochainComplex (ModuleCat.{u} A) ℤ :=
  (rowOverSpecFunctor f U).obj (SheafOfModules.relativeModule F f.toShHom)

/-- In a nonnegative degree, `rowOverSpec` is the scalar restriction of the product of
section modules on the corresponding finite intersections of the cover. -/
theorem rowOverSpec_obj (f : X ⟶ Spec (CommRingCat.of A)) {ι : Type u}
    (U : ι → X.Opens) (F : X.Modules) (n : ℕ) :
    IsIsomorphic ((rowOverSpec f U F).X (n : ℤ))
      ((ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap f)).obj
        (∏ᶜ fun j : SheafOfModules.RingedSite.Cech.Index (⊤ : X.Opens)
            (fun i ↦ Over.mk (Opens.leTop (U i))) n ↦
          SheafOfModules.RingedSite.Cech.moduleSummand X.ringCatSheaf (⊤ : X.Opens)
            (fun i ↦ Over.mk (Opens.leTop (U i)))
            ((SheafOfModules.forget X.ringCatSheaf).obj F) n j)) := sorry

/-- The bicomplex obtained by applying the affine-base Čech-row functor to every term and
differential of a complex of `f⁻¹𝒪_(Spec A)`-modules. -/
abbrev bicomplexOverSpec (f : X ⟶ Spec (CommRingCat.of A)) {ι : Type u}
    (U : ι → X.Opens)
    (K : CochainComplex (relativeSpace f.toShHom).Modules ℤ) :
    HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  ((rowOverSpecFunctor f U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- The complex-direction differential of `bicomplexOverSpec` is the Čech-row image of the
corresponding `f⁻¹𝒪_(Spec A)`-linear differential. -/
theorem bicomplexOverSpec_d (f : X ⟶ Spec (CommRingCat.of A)) {ι : Type u}
    (U : ι → X.Opens)
    (K : CochainComplex (relativeSpace f.toShHom).Modules ℤ) (i j : ℤ) :
    (bicomplexOverSpec f U K).d i j = (rowOverSpecFunctor f U).map (K.d i j) := sorry

/-- For a finite affine open cover with affine nonempty finite intersections, the total ordinary
Čech complex of a bounded coefficient-linear complex with relatively flat quasicoherent terms
is K-flat over the affine base ring. -/
@[stacks 0FMQ]
theorem total_isKFlat
    {A : Type u} [CommRing A] {X : _root_.AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (hAffine : ∀ p : ℕ, ∀ σ : Fin (p + 1) → ι,
      IsAffineOpen (⨅ a, U (σ a)))
    (F : ℤ → X.Modules)
    [hQuasicoherent : ∀ n, (F n).IsQuasicoherent]
    [hFlat : ∀ n, SheafOfModules.IsFlatOver (F n) f.toShHom]
    (K : CochainComplex (relativeSpace f.toShHom).Modules ℤ)
    (termIso : ∀ n, K.X n ≅ SheafOfModules.relativeModule (F n) f.toShHom)
    (hBounded : CochainComplex.bounded _ K) :
    ((bicomplexOverSpec f U K).total (ComplexShape.up ℤ)).IsKFlat := sorry

end AlgebraicGeometry.Scheme.ModuleCech
