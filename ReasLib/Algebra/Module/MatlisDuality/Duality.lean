module

public import ReasLib.Algebra.Category.ModuleCat.ChainConditions
public import ReasLib.Algebra.Module.Injective.Hull
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Bidual
public import ReasLib.RingTheory.Completion.LocalRing
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite

namespace LinearMap.IsInjectiveHull

variable (R E : Type u) [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
  [AddCommGroup E] [Module R E] [Module.Injective R E]
  {ι : IsLocalRing.ResidueField R →ₗ[R] E} (hι : ι.IsInjectiveHull)

include hι

/-- Dualization into a chosen injective hull sends Artinian modules to Noetherian modules. -/
theorem dualIsNoetherian (M : (ArtinianModuleCat R)ᵒᵖ) :
    (isNoetherianObject : ObjectProperty (ModuleCat.{u} R))
      ((((isArtinianObject : ObjectProperty (ModuleCat.{u} R)).ι.op) ⋙
        (RightInternalHom.ofBraidedClosed : RightInternalHom (ModuleCat.{u} R)).dualFunctor
          (ModuleCat.of R E)).obj M) := sorry

/-- Dualization into a chosen injective hull sends Noetherian modules to Artinian modules. -/
theorem dualIsArtinian (M : (NoetherianModuleCat R)ᵒᵖ) :
    (isArtinianObject : ObjectProperty (ModuleCat.{u} R))
      ((((isNoetherianObject : ObjectProperty (ModuleCat.{u} R)).ι.op) ⋙
        (RightInternalHom.ofBraidedClosed : RightInternalHom (ModuleCat.{u} R)).dualFunctor
          (ModuleCat.of R E)).obj M) := sorry

/-- Matlis dualization from Artinian modules to Noetherian modules. -/
def artinianDual : (ArtinianModuleCat R)ᵒᵖ ⥤ NoetherianModuleCat R :=
  ObjectProperty.lift (isNoetherianObject : ObjectProperty (ModuleCat.{u} R))
    (((isArtinianObject : ObjectProperty (ModuleCat.{u} R)).ι.op) ⋙
      (RightInternalHom.ofBraidedClosed : RightInternalHom (ModuleCat.{u} R)).dualFunctor
        (ModuleCat.of R E))
    (dualIsNoetherian R E hι)

/-- Matlis dualization from Noetherian modules to Artinian modules. -/
def noetherianDual : (NoetherianModuleCat R)ᵒᵖ ⥤ ArtinianModuleCat R :=
  ObjectProperty.lift (isArtinianObject : ObjectProperty (ModuleCat.{u} R))
    (((isNoetherianObject : ObjectProperty (ModuleCat.{u} R)).ι.op) ⋙
      (RightInternalHom.ofBraidedClosed : RightInternalHom (ModuleCat.{u} R)).dualFunctor
        (ModuleCat.of R E))
    (dualIsArtinian R E hι)

/-- The underlying module of the Matlis dual of an Artinian module is its module of linear maps
into the chosen injective hull. -/
theorem artinianDual_obj (M : (ArtinianModuleCat R)ᵒᵖ) :
    ((artinianDual R E hι).obj M).obj = ModuleCat.of R (M.unop →ₗ[R] E) := sorry

/-- The underlying module of the Matlis dual of a Noetherian module is its module of linear maps
into the chosen injective hull. -/
theorem noetherianDual_obj (M : (NoetherianModuleCat R)ᵒᵖ) :
    ((noetherianDual R E hι).obj M).obj = ModuleCat.of R (M.unop →ₗ[R] E) := sorry

/-- Matlis dualization on Artinian modules acts on morphisms by precomposition. -/
theorem artinianDual_map_apply {M N : ArtinianModuleCat R} (f : M ⟶ N)
    (g : N →ₗ[R] E) (x : M) :
    ((artinianDual R E hι).map f.op (ModuleCat.ofHom g)).hom x = g (f x) := sorry

/-- Matlis dualization on Noetherian modules acts on morphisms by precomposition. -/
theorem noetherianDual_map_apply {M N : NoetherianModuleCat R} (f : M ⟶ N)
    (g : N →ₗ[R] E) (x : M) :
    ((noetherianDual R E hι).map f.op (ModuleCat.ofHom g)).hom x = g (f x) := sorry

/-- Covariant double Matlis dualization on Artinian modules. -/
abbrev artinianBidual : ArtinianModuleCat R ⥤ ArtinianModuleCat R :=
  (artinianDual R E hι).rightOp ⋙ noetherianDual R E hι

/-- Covariant double Matlis dualization on Noetherian modules. -/
abbrev noetherianBidual : NoetherianModuleCat R ⥤ NoetherianModuleCat R :=
  (noetherianDual R E hι).rightOp ⋙ artinianDual R E hι

/-- The canonical evaluation morphism from an Artinian module to its double Matlis dual. -/
def artinianEvaluationApp (M : ArtinianModuleCat R) :
    M ⟶ (artinianBidual R E hι).obj M :=
  ObjectProperty.homMk
    (((RightInternalHom.ofBraidedClosed : RightInternalHom (ModuleCat.{u} R)).toBidual
      (ModuleCat.of R E)).app M.obj)

/-- The canonical evaluation morphism from a Noetherian module to its double Matlis dual. -/
def noetherianEvaluationApp (M : NoetherianModuleCat R) :
    M ⟶ (noetherianBidual R E hι).obj M :=
  ObjectProperty.homMk
    (((RightInternalHom.ofBraidedClosed : RightInternalHom (ModuleCat.{u} R)).toBidual
      (ModuleCat.of R E)).app M.obj)

/-- The Artinian-side canonical bidual morphism evaluates a functional at the module element. -/
theorem artinianEvaluationApp_apply (M : ArtinianModuleCat R) (m : M)
    (f : M →ₗ[R] E) :
    (artinianEvaluationApp R E hι M m).hom (ModuleCat.ofHom f) = f m := sorry

/-- The Noetherian-side canonical bidual morphism evaluates a functional at the module element. -/
theorem noetherianEvaluationApp_apply (M : NoetherianModuleCat R) (m : M)
    (f : M →ₗ[R] E) :
    (noetherianEvaluationApp R E hι M m).hom (ModuleCat.ofHom f) = f m := sorry

/-- The canonical bidual evaluation morphisms are natural on Artinian modules. -/
theorem artinianEvaluation_naturality {M N : ArtinianModuleCat R} (f : M ⟶ N) :
    f ≫ artinianEvaluationApp R E hι N =
      artinianEvaluationApp R E hι M ≫ (artinianBidual R E hι).map f := sorry

/-- The canonical bidual evaluation morphisms are natural on Noetherian modules. -/
theorem noetherianEvaluation_naturality {M N : NoetherianModuleCat R} (f : M ⟶ N) :
    f ≫ noetherianEvaluationApp R E hι N =
      noetherianEvaluationApp R E hι M ≫ (noetherianBidual R E hι).map f := sorry

/-- The canonical natural transformation from the identity to double Matlis dualization on
Artinian modules. -/
def artinianEvaluation : 𝟭 (ArtinianModuleCat R) ⟶ artinianBidual R E hι where
  app M := artinianEvaluationApp R E hι M
  naturality M N f := artinianEvaluation_naturality R E hι f

/-- The canonical natural transformation from the identity to double Matlis dualization on
Noetherian modules. -/
def noetherianEvaluation : 𝟭 (NoetherianModuleCat R) ⟶ noetherianBidual R E hι where
  app M := noetherianEvaluationApp R E hι M
  naturality M N f := noetherianEvaluation_naturality R E hι f

/-- Matlis dualization from Artinian modules is an equivalence onto Noetherian modules. -/
theorem artinianDualIsEquivalence :
    Functor.IsEquivalence (artinianDual R E hι) := sorry

/-- Matlis dualization from Noetherian modules is an equivalence onto Artinian modules. -/
theorem noetherianDualIsEquivalence :
    Functor.IsEquivalence (noetherianDual R E hι) := sorry

/-- The Artinian bidual evaluation is an isomorphism. -/
theorem artinianEvaluationIsIso : IsIso (artinianEvaluation R E hι) := sorry

/-- The Noetherian bidual evaluation is an isomorphism. -/
theorem noetherianEvaluationIsIso : IsIso (noetherianEvaluation R E hι) := sorry

end LinearMap.IsInjectiveHull
