/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import ReasLib.Algebra.Module.MatlisDuality.Artinian
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Bidual

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite

namespace Module.Finite

variable (R E : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
  [AddCommGroup E] [Module R E] [Module.Injective R E]
  (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : ι.IsInjectiveHull)

include hι

/-- The linear dual into an injective hull of the residue field is finite for every
finitely generated module over an Artinian local ring. -/
theorem dual_of_injectiveHull (M : FGModuleCat.{u} R) : Module.Finite R (M →ₗ[R] E) := sorry

end Module.Finite

namespace LinearMap.IsInjectiveHull

variable (R E : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
  [AddCommGroup E] [Module R E] [Module.Injective R E]
  (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : ι.IsInjectiveHull)

include hι

/-- The ambient dual functor sends finite modules to finite modules. -/
theorem dualFunctorObjFinite (M : (FGModuleCat.{u} R)ᵒᵖ) :
    ModuleCat.isFG R
      (((ModuleCat.isFG R).ι.op ⋙
        (RightInternalHom.ofBraidedClosed : RightInternalHom (ModuleCat.{u} R)).dualFunctor
          (ModuleCat.of R E)).obj M) := sorry

/-- Contravariant dualization into an injective hull, restricted to finitely generated modules. -/
def dualFunctor : (FGModuleCat.{u} R)ᵒᵖ ⥤ FGModuleCat.{u} R :=
  ObjectProperty.lift (ModuleCat.isFG R)
    ((ModuleCat.isFG R).ι.op ⋙
      (RightInternalHom.ofBraidedClosed : RightInternalHom (ModuleCat.{u} R)).dualFunctor
        (ModuleCat.of R E))
    (dualFunctorObjFinite R E ι hι)

/-- The underlying module of the restricted dual is the module of linear maps into the chosen
injective hull. -/
theorem dualFunctor_obj (M : (FGModuleCat.{u} R)ᵒᵖ) :
    ((dualFunctor R E ι hι).obj M).obj = ModuleCat.of R (M.unop →ₗ[R] E) := sorry

/-- The restricted dual functor acts on morphisms by precomposition. -/
theorem dualFunctor_map_apply {M N : FGModuleCat.{u} R} (f : M ⟶ N)
    (g : N →ₗ[R] E) (x : M) :
    ((dualFunctor R E ι hι).map f.op (ModuleCat.ofHom g)).hom x = g (f x) := sorry

/-- Covariant double dualization on finitely generated modules. -/
abbrev bidualFunctor : FGModuleCat.{u} R ⥤ FGModuleCat.{u} R :=
  (dualFunctor R E ι hι).rightOp ⋙ dualFunctor R E ι hι

/-- The canonical evaluation morphism from a finite module to its double dual. -/
def evaluationApp (M : FGModuleCat.{u} R) :
    M ⟶ (bidualFunctor R E ι hι).obj M :=
  ObjectProperty.homMk
    (((RightInternalHom.ofBraidedClosed : RightInternalHom (ModuleCat.{u} R)).toBidual
      (ModuleCat.of R E)).app M.obj)

/-- The canonical bidual morphism evaluates a functional at the given module element. -/
theorem evaluationApp_apply (M : FGModuleCat.{u} R) (m : M) (f : M →ₗ[R] E) :
    (evaluationApp R E ι hι M m).hom (ModuleCat.ofHom f) = f m := sorry

/-- The canonical bidual evaluation morphisms are natural on finite modules. -/
theorem evaluation_naturality {M N : FGModuleCat.{u} R} (f : M ⟶ N) :
    f ≫ evaluationApp R E ι hι N =
      evaluationApp R E ι hι M ≫ (bidualFunctor R E ι hι).map f := sorry

/-- The canonical natural transformation from the identity to double dualization on finite
modules. -/
def evaluation : 𝟭 (FGModuleCat.{u} R) ⟶ bidualFunctor R E ι hι where
  app M := evaluationApp R E ι hι M
  naturality M N f := evaluation_naturality R E ι hι f

/-- Every finite module is identified with its double dual by canonical evaluation. -/
instance evaluationIsIso : IsIso (evaluation R E ι hι) := sorry

/-- Dualization into an injective hull is an anti-equivalence on finitely generated modules. -/
instance dualFunctorIsEquivalence :
    Functor.IsEquivalence (dualFunctor R E ι hι) := sorry

/-- Dualization into an injective hull is exact on finitely generated modules. -/
theorem dualFunctor_exact :
    exactFunctor (FGModuleCat.{u} R)ᵒᵖ (FGModuleCat.{u} R)
      (dualFunctor R E ι hι) := sorry

end LinearMap.IsInjectiveHull
