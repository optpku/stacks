/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.GlobalSections.FiniteProjective
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace ComplexShape
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Remark 75.25.2. A single bounded finite-projective complex computes derived global
sections of the ordinary base-changed module, functorially in the base algebra. -/
@[stacks 0A1Q] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.exists_finiteProjective_globalSections_baseChange :
    ∀ {R : Type u} [CommRing R]
      {X : AlgebraicSpace (Spec (CommRingCat.of R))}
    [FinitePresentation (SchemeRealization.toBase X)] (G : X.Modules) [G.IsFinitePresentation]
    (hflat : ∀ x, flatOverAt G (SchemeRealization.toBase X) x)
    (hsupport : ClosedSubset.ProperOver (SchemeRealization.toBase X)
      (Closeds.closure (moduleSupport G))),
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
              (i B XB gB fB sqB).hom)))
