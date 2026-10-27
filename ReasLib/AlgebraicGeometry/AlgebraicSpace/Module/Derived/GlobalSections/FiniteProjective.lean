/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.CoefficientMap
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.GlobalSections.AffineBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Single
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubset.Proper

/-! # Finite-projective models for affine-valued derived global sections -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace ComplexShape
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {R : Type u} [CommRing R]
variable {X : AlgebraicSpace (Spec (CommRingCat.of R))}

/-- Derived global sections over the base ring of a module placed in degree zero. -/
abbrev affineModuleDerivedGlobalSections (G : X.Modules) :
    DerivedCategory (ModuleCat.{u} R) :=
  (AffineGlobalSections.functor (SchemeRealization.toBase X)).obj
    ((DerivedCategory.singleFunctor X.Modules 0).obj G)

/-- Derived global sections of a module are the affine global-sections functor
evaluated on its degree-zero realization. -/
theorem affineModuleDerivedGlobalSections_obj (G : X.Modules) :
    affineModuleDerivedGlobalSections G =
      (AffineGlobalSections.functor (SchemeRealization.toBase X)).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj G) := rfl

/-- Derived global sections over a base algebra of the ordinary pullback module. -/
def affineModuleDerivedGlobalSectionsBaseChange
    {A : Type u} [CommRing A] [Algebra R A]
    {X' : AlgebraicSpace (Spec (CommRingCat.of R))} (g' : X' ⟶ X)
    (f' : X' ⟶ ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))))
    (G : X.Modules) : DerivedCategory (ModuleCat.{u} A) :=
  (AffineGlobalSections.functor f').obj
    ((DerivedCategory.singleFunctor X'.Modules 0).obj ((pullback g').obj G))

/-- Base-changed global sections evaluate the degree-zero ordinary pullback. -/
theorem affineModuleDerivedGlobalSectionsBaseChange_obj
    {A : Type u} [CommRing A] [Algebra R A]
    {X' : AlgebraicSpace (Spec (CommRingCat.of R))} (g' : X' ⟶ X)
    (f' : X' ⟶ ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))))
    (G : X.Modules) :
    affineModuleDerivedGlobalSectionsBaseChange g' f' G =
      (AffineGlobalSections.functor f').obj
        ((DerivedCategory.singleFunctor X'.Modules 0).obj ((pullback g').obj G)) := rfl

/-- Scalar base change followed by the canonical comparison from derived to ordinary
module pullback gives the module global-sections base-change map. -/
def affineModuleBaseChangeMap
    {A : Type u} [CommRing A] [Algebra R A]
    {X' : AlgebraicSpace (Spec (CommRingCat.of R))} (g' : X' ⟶ X)
    (f' : X' ⟶ ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))))
    (sq : CommSq g' f' (SchemeRealization.toBase X)
      (Hom.specMap (CommRingCat.ofHom (algebraMap R A)))) (G : X.Modules) :
    (ModuleCat.derivedExtensionOfScalars (algebraMap R A)).obj
        (affineModuleDerivedGlobalSections G) ⟶
      affineModuleDerivedGlobalSectionsBaseChange g' f' G :=
  AffineGlobalSections.pullbackMap sq ((DerivedCategory.singleFunctor X.Modules 0).obj G) ≫
    (AffineGlobalSections.functor f').map (ModuleDerived.singlePullbackComparison g' G 0)

/-- The global-sections transition along an algebra homomorphism is the scalar unit
followed by geometric pullback and the ordinary pullback composition identification. -/
def affineModuleGlobalSectionsTransition
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (ψ : A →ₐ[R] B)
    {XA XB : AlgebraicSpace (Spec (CommRingCat.of R))}
    (gA : XA ⟶ X) (gB : XB ⟶ X)
    (fA : XA ⟶ ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))))
    (fB : XB ⟶ ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)))))
    (h : XB ⟶ XA) (hg : h ≫ gA = gB)
    (sq : CommSq h fB fA
      (ofOverHomMk (Spec.map (CommRingCat.ofHom ψ.toRingHom)) (by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        exact congrArg (fun σ : R →+* B ↦ Spec.map (CommRingCat.ofHom σ))
          ψ.comp_algebraMap)))
    (G : X.Modules) :
    affineModuleDerivedGlobalSectionsBaseChange gA fA G ⟶
      (ModuleCat.derivedRestrictionOfScalars ψ.toRingHom).obj
        (affineModuleDerivedGlobalSectionsBaseChange gB fB G) :=
  (ModuleCat.derivedExtensionRestrictionAdjunction ψ.toRingHom).unit.app
      (affineModuleDerivedGlobalSectionsBaseChange gA fA G) ≫
    (ModuleCat.derivedRestrictionOfScalars ψ.toRingHom).map
      (AffineGlobalSections.pullbackMap sq
          ((DerivedCategory.singleFunctor XA.Modules 0).obj ((pullback gA).obj G)) ≫
        (AffineGlobalSections.functor fB).map
          (ModuleDerived.singlePullbackComparison h ((pullback gA).obj G) 0 ≫
            (DerivedCategory.singleFunctor XB.Modules 0).map
              ((pullbackCompIso h gA).hom.app G ≫
                eqToHom (congrArg (fun g ↦ (pullback g).obj G) hg))))

/-- A finitely presented module, flat over the base ring with proper support on a
finitely presented algebraic space, has perfect derived global sections. -/
theorem globalSectionsOver_isPerfect_of_finitePresentation
    [FinitePresentation (SchemeRealization.toBase X)] (G : X.Modules) [G.IsFinitePresentation]
    (hflat : ∀ x, flatOverAt G (SchemeRealization.toBase X) x)
    (hsupport : ClosedSubset.ProperOver (SchemeRealization.toBase X)
      (Closeds.closure (moduleSupport G))) :
    DerivedCategory.IsPerfect (affineModuleDerivedGlobalSections G) := sorry

/-- The canonical global-sections base-change map for a finitely presented module
flat over the base with proper support is invertible for every cartesian affine base change. -/
theorem globalSectionsOver_baseChange_isIso_of_finitePresentation
    [FinitePresentation (SchemeRealization.toBase X)] (G : X.Modules) [G.IsFinitePresentation]
    (hflat : ∀ x, flatOverAt G (SchemeRealization.toBase X) x)
    (hsupport : ClosedSubset.ProperOver (SchemeRealization.toBase X)
      (Closeds.closure (moduleSupport G)))
    {A : Type u} [CommRing A] [Algebra R A]
    {X' : AlgebraicSpace (Spec (CommRingCat.of R))} (g' : X' ⟶ X)
    (f' : X' ⟶ ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))))
    (sq : IsPullback g' f' (SchemeRealization.toBase X)
      (Hom.specMap (CommRingCat.ofHom (algebraMap R A)))) :
    IsIso (affineModuleBaseChangeMap g' f' sq.toCommSq G) := sorry

/-- A finitely presented module flat over the base ring with proper support on a
finitely presented algebraic space admits one bounded finite-projective complex computing
its global sections after every base-algebra extension, compatibly with the canonical
base-change map and naturally in homomorphisms of base algebras. -/
theorem exists_finiteProjective_globalSections_baseChange
    [FinitePresentation (SchemeRealization.toBase X)] (G : X.Modules) [G.IsFinitePresentation]
    (hflat : ∀ x, flatOverAt G (SchemeRealization.toBase X) x)
    (hsupport : ClosedSubset.ProperOver (SchemeRealization.toBase X)
      (Closeds.closure (moduleSupport G))) :
    ∃ (M : CochainComplex (ModuleCat.{u} R) ℤ),
      CochainComplex.IsBoundedFiniteProjective M ∧
      ∃ (e : affineModuleDerivedGlobalSections G ≅ DerivedCategory.Q.obj M)
        (i : ∀ (A : Type u) [CommRing A] [Algebra R A]
          (XA : AlgebraicSpace (Spec (CommRingCat.of R))) (gA : XA ⟶ X)
          (fA : XA ⟶ ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))))
          (sqA : IsPullback gA fA (SchemeRealization.toBase X)
            (Hom.specMap (CommRingCat.ofHom (algebraMap R A)))),
          affineModuleDerivedGlobalSectionsBaseChange gA fA G ≅
            DerivedCategory.Q.obj
              (((ModuleCat.extendScalars (algebraMap R A)).mapHomologicalComplex (up ℤ)).obj M)),
        (∀ (A : Type u) [CommRing A] [Algebra R A]
          (XA : AlgebraicSpace (Spec (CommRingCat.of R))) (gA : XA ⟶ X)
          (fA : XA ⟶ ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))))
          (sqA : IsPullback gA fA (SchemeRealization.toBase X)
            (Hom.specMap (CommRingCat.ofHom (algebraMap R A)))),
          affineModuleBaseChangeMap gA fA sqA.toCommSq G ≫ (i A XA gA fA sqA).hom =
            (ModuleCat.derivedExtensionOfScalars (algebraMap R A)).map e.hom ≫
              (ModuleCat.derivedExtensionComplexCounit (algebraMap R A)).app M) ∧
        (∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
          (ψ : A →ₐ[R] B)
          (XA XB : AlgebraicSpace (Spec (CommRingCat.of R))) (gA : XA ⟶ X) (gB : XB ⟶ X)
          (fA : XA ⟶ ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))))
          (fB : XB ⟶ ofOver (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)))))
          (sqA : IsPullback gA fA (SchemeRealization.toBase X)
            (Hom.specMap (CommRingCat.ofHom (algebraMap R A))))
          (sqB : IsPullback gB fB (SchemeRealization.toBase X)
            (Hom.specMap (CommRingCat.ofHom (algebraMap R B))))
          (h : XB ⟶ XA) (hg : h ≫ gA = gB)
          (sqh : CommSq h fB fA
            (ofOverHomMk (Spec.map (CommRingCat.ofHom ψ.toRingHom)) (by
              rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
              exact congrArg (fun σ : R →+* B ↦ Spec.map (CommRingCat.ofHom σ))
                ψ.comp_algebraMap))),
          CommSq (i A XA gA fA sqA).hom
            (affineModuleGlobalSectionsTransition ψ gA gB fA fB h hg sqh G)
            (ModuleCat.derivedCochainScalarExtensionMap (algebraMap R A) ψ.toRingHom
              (algebraMap R B) ψ.comp_algebraMap M)
            ((ModuleCat.derivedRestrictionOfScalars ψ.toRingHom).map
              (i B XB gB fB sqB).hom)) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
