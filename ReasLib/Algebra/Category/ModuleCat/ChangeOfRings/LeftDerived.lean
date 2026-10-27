/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Projective

/-!
# Left-derived change of rings

Projective resolutions give comparison maps for extension of scalars and its composites
along maps of commutative rings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section

universe u

namespace CommAlgCat.Over.Polynomial.Site

/-- A chain-map comparison from the image of a chosen projective resolution under extension of
scalars to the chosen projective resolution of the extended module. -/
def mapExtendScalarsToResolution {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (M : ModuleCat.{u} R) :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (projectiveResolution M).complex ⟶
      (projectiveResolution ((ModuleCat.extendScalars φ).obj M)).complex :=
  let P := projectiveResolution M
  let Q := projectiveResolution ((ModuleCat.extendScalars φ).obj M)
  let K := (ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.down ℕ) |>.obj P.complex
  -- Local instance justification (proof-local temporary data): projectivity of `K.X 1` is a field of the chosen `ProjectiveResolution`, not a global instance.
  letI : Projective (K.X 1) :=
    (ModuleCat.extendScalars φ).projective_obj_of_projective (P.projective 1)
  ChainComplex.mkHom K Q.complex
    (@Projective.factorThru (ModuleCat.{u} S) _ (K.X 0)
      ((ModuleCat.extendScalars φ).obj M) (Q.complex.X 0)
      ((ModuleCat.extendScalars φ).projective_obj_of_projective (P.projective 0))
      ((ModuleCat.extendScalars φ).map (P.π.f 0)) (Q.π.f 0)
      (epi_of_isColimit_cofork Q.isColimitCokernelCofork))
    (Q.exact₀.liftFromProjective
      (K.d 1 0 ≫
        @Projective.factorThru (ModuleCat.{u} S) _ (K.X 0)
          ((ModuleCat.extendScalars φ).obj M) (Q.complex.X 0)
          ((ModuleCat.extendScalars φ).projective_obj_of_projective (P.projective 0))
          ((ModuleCat.extendScalars φ).map (P.π.f 0)) (Q.π.f 0)
          (epi_of_isColimit_cofork Q.isColimitCokernelCofork))
      sorry)
    sorry
    fun n p ↦
      -- Local instance justification (proof-local temporary data): projectivity of `K.X (n + 2)` is a field of the chosen `ProjectiveResolution`, not a global instance.
      letI : Projective (K.X (n + 2)) :=
        (ModuleCat.extendScalars φ).projective_obj_of_projective (P.projective (n + 2))
      ⟨(Q.exact_succ n).liftFromProjective (K.d (n + 2) (n + 1) ≫ p.2.1) sorry, sorry⟩

/-- The canonical comparison from left-derived of a composite extension of scalars to the
postcomposed left-derived functor. -/
def leftDerivedCompToPostcomposed {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : S →+* T) (n : ℕ) (M : ModuleCat.{u} R) :
    ((ModuleCat.extendScalars φ ⋙ ModuleCat.extendScalars ψ).leftDerived n).obj M ⟶
      ((ModuleCat.extendScalars ψ).leftDerived n).obj ((ModuleCat.extendScalars φ).obj M) :=
  ((projectiveResolution M).isoLeftDerivedObj
      (ModuleCat.extendScalars φ ⋙ ModuleCat.extendScalars ψ) n).hom ≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} T) (ComplexShape.down ℕ) n).map
      (((ModuleCat.extendScalars ψ).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (mapExtendScalarsToResolution φ M)) ≫
    ((projectiveResolution ((ModuleCat.extendScalars φ).obj M)).isoLeftDerivedObj
      (ModuleCat.extendScalars ψ) n).inv

end CommAlgCat.Over.Polynomial.Site
