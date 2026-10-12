/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Affine
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 36.7.3 (1): on `Spec A`, the coherator is naturally isomorphic to affine global
sections followed by the associated quasicoherent module functor. -/
@[stacks 08D9] #check
  (AlgebraicGeometry.Scheme.QCoh.affineCoherator_isomorphic :
    ∀ (A : CommRingCat.{u}),
      IsIsomorphic (AlgebraicGeometry.Scheme.QCoh.coherator (AlgebraicGeometry.Spec A))
        ((AlgebraicGeometry.moduleSpecΓFunctor :
            (AlgebraicGeometry.Spec A).Modules ⥤ ModuleCat A) ⋙
          (AlgebraicGeometry.tildeEquiv :
            ModuleCat A ≌
              AlgebraicGeometry.Scheme.QCoh (AlgebraicGeometry.Spec A)).functor))

/- Lemma 36.7.3 (2): on `Spec A`, the derived coherator is naturally isomorphic to derived
global sections, restriction along `A ≅ Γ(Spec A, 𝒪)`, and the derived associated-module
functor. -/
@[stacks 08D9] #check
  (AlgebraicGeometry.Scheme.QCoh.Derived.affineCoherator_isomorphic :
    ∀ (A : CommRingCat.{u}),
      IsIsomorphic
        (AlgebraicGeometry.Scheme.QCoh.Derived.coherator (AlgebraicGeometry.Spec A))
        ((AlgebraicGeometry.Scheme.Modules.ringedSpaceEquivalence
              (AlgebraicGeometry.Spec A)).mapDerivedCategory.functor ⋙
          AlgebraicGeometry.RingedSpace.moduleDerivedGlobalSections
            (AlgebraicGeometry.Spec A).toRingedSpace ⋙
          ModuleCat.derivedRestrictionOfScalars
            (AlgebraicGeometry.Scheme.ΓSpecIso A).inv.hom ⋙
          (AlgebraicGeometry.tildeEquiv :
            ModuleCat A ≌ AlgebraicGeometry.Scheme.QCoh
              (AlgebraicGeometry.Spec A)).mapDerivedCategory.functor))

/- Lemma 36.7.3 (3): on `Spec A`, the derived coherator restricted to objects with
quasicoherent cohomology is a quasi-inverse to the canonical comparison functor. -/
@[stacks 08D9] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.affineCoherator_isQuasiInverse :
    ∀ (A : CommRingCat.{u}),
      (AlgebraicGeometry.Scheme.DerivedQCoh.comparison
          (AlgebraicGeometry.Spec A)).IsQuasiInverse
        ((DerivedCategory.cohomologyIn
              (AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty
                (AlgebraicGeometry.Spec A).toRingedSpace)).ι ⋙
          (AlgebraicGeometry.Scheme.Modules.ringedSpaceEquivalence
              (AlgebraicGeometry.Spec A)).mapDerivedCategory.inverse ⋙
          AlgebraicGeometry.Scheme.QCoh.Derived.coherator (AlgebraicGeometry.Spec A)))
