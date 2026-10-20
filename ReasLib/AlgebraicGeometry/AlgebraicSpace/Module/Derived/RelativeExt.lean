module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Shift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor.Bifunctor

/-! # Relative Ext functors on algebraic spaces -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.DerivedCategory ComplexShape
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Fixed-left derived tensor is naturally isomorphic to fixed-right derived tensor
through the canonical braiding and the fixed-right model comparison. -/
private def tensorLeftIsoRight (E : ModuleDerived X) :
    DerivedTensor.Bifunctor.leftFunctor E ≅ DerivedTensor.Right.functor E :=
  (Functor.curry.mapIso (DerivedTensor.Bifunctor.braiding (C := Modules X))).app E ≪≫
    (DerivedTensor.Bifunctor.Right.iso E).symm

/-- Pull back a derived module along `f` and tensor it on the left with `E`. -/
def tensorPullback (f : X ⟶ Y) (E : ModuleDerived X) :
    ModuleDerived Y ⥤ ModuleDerived X :=
  pullback f ⋙ DerivedTensor.Bifunctor.leftFunctor E

/-- Derived pullback followed by tensor with a fixed left factor commutes with shifts. -/
@[no_expose] instance tensorPullback_commShift (f : X ⟶ Y) (E : ModuleDerived X) :
    (tensorPullback f E).CommShift ℤ :=
  Functor.CommShift.ofIso
    (Functor.isoWhiskerLeft (pullback f) (tensorLeftIsoRight E).symm) ℤ

/-- The coefficient functor sends `F` to `E ⊗ᴸ Lf*(F[0])`. -/
def relativeExtCoefficients (f : X ⟶ Y) (E : ModuleDerived X) :
    Modules Y ⥤ ModuleDerived X :=
  DerivedCategory.singleFunctor (Modules Y) 0 ⋙ tensorPullback f E

/-- The Ext boundary for a short exact sequence is composition with its canonical
connecting morphism in the derived category. -/
def representedExtBoundary (L : ModuleDerived Y) (s : ShortComplex (Modules Y))
    (hs : s.ShortExact) (i : ℤ) :
    Ext⁽i⁾(L, (DerivedCategory.singleFunctor (Modules Y) 0).obj s.X₃) →
      Ext⁽i + 1⁾(L, (DerivedCategory.singleFunctor (Modules Y) 0).obj s.X₁) :=
  fun x ↦ ShiftedHom.comp x
    (DerivedCategory.triangleOfSES
      (hs.map_of_exact (HomologicalComplex.single (Modules Y) (up ℤ) 0))).mor₃
    (add_comm 1 i)

/-- The relative Ext boundary is composition with the connecting morphism after
derived pullback and tensor with `E`. -/
def relativeExtBoundary (f : X ⟶ Y) (K E : ModuleDerived X)
    (s : ShortComplex (Modules Y)) (hs : s.ShortExact) (i : ℤ) :
    Ext⁽i⁾(K, (relativeExtCoefficients f E).obj s.X₃) →
      Ext⁽i + 1⁾(K, (relativeExtCoefficients f E).obj s.X₁) :=
  fun x ↦ ShiftedHom.comp x
    (ShiftedHom.map (DerivedCategory.triangleOfSES
      (hs.map_of_exact (HomologicalComplex.single (Modules Y) (up ℤ) 0))).mor₃
      (tensorPullback f E)) (add_comm 1 i)

/-- A complex represents relative Ext if additive equivalences in every integer degree
are natural on quasi-coherent coefficients and commute with short-exact-sequence boundaries. -/
def RepresentsRelativeExt (f : X ⟶ Y) (K E : ModuleDerived X)
    (L : ModuleDerived Y) : Prop :=
  ∃ α : ∀ (F : Modules Y) (_ : quasiCoherentModuleProperty Y F) (i : ℤ),
      Ext⁽i⁾(L, (DerivedCategory.singleFunctor (Modules Y) 0).obj F) ≃+
        Ext⁽i⁾(K, (relativeExtCoefficients f E).obj F),
    (∀ {F F' : Modules Y} (φ : F ⟶ F')
        (hF : quasiCoherentModuleProperty Y F) (hF' : quasiCoherentModuleProperty Y F')
        (i : ℤ) (x : Ext⁽i⁾(L, (DerivedCategory.singleFunctor (Modules Y) 0).obj F)),
      α F' hF' i (x ≫ ((DerivedCategory.singleFunctor (Modules Y) 0).map φ)⟦i⟧') =
        α F hF i x ≫ ((relativeExtCoefficients f E).map φ)⟦i⟧') ∧
    (∀ (s : ShortComplex (Modules Y)) (hs : s.ShortExact)
        (hF₁ : quasiCoherentModuleProperty Y s.X₁)
        (hF₂ : quasiCoherentModuleProperty Y s.X₂)
        (hF₃ : quasiCoherentModuleProperty Y s.X₃) (i : ℤ)
        (x : Ext⁽i⁾(L, (DerivedCategory.singleFunctor (Modules Y) 0).obj s.X₃)),
      α s.X₁ hF₁ (i + 1) (representedExtBoundary L s hs i x) =
        relativeExtBoundary f K E s hs i (α s.X₃ hF₃ i x))

/-- Relative Ext representability is equivalent to the full naturality and boundary
compatibility criterion for a family of additive equivalences. -/
theorem representsRelativeExt_iff (f : X ⟶ Y) (K E : ModuleDerived X)
    (L : ModuleDerived Y) :
    RepresentsRelativeExt f K E L ↔
  ∃ α : ∀ (F : Modules Y) (_ : quasiCoherentModuleProperty Y F) (i : ℤ),
      Ext⁽i⁾(L, (DerivedCategory.singleFunctor (Modules Y) 0).obj F) ≃+
        Ext⁽i⁾(K, (relativeExtCoefficients f E).obj F),
    (∀ {F F' : Modules Y} (φ : F ⟶ F')
        (hF : quasiCoherentModuleProperty Y F) (hF' : quasiCoherentModuleProperty Y F')
        (i : ℤ) (x : Ext⁽i⁾(L, (DerivedCategory.singleFunctor (Modules Y) 0).obj F)),
      α F' hF' i (x ≫ ((DerivedCategory.singleFunctor (Modules Y) 0).map φ)⟦i⟧') =
        α F hF i x ≫ ((relativeExtCoefficients f E).map φ)⟦i⟧') ∧
    (∀ (s : ShortComplex (Modules Y)) (hs : s.ShortExact)
        (hF₁ : quasiCoherentModuleProperty Y s.X₁)
        (hF₂ : quasiCoherentModuleProperty Y s.X₂)
        (hF₃ : quasiCoherentModuleProperty Y s.X₃) (i : ℤ)
        (x : Ext⁽i⁾(L, (DerivedCategory.singleFunctor (Modules Y) 0).obj s.X₃)),
      α s.X₁ hF₁ (i + 1) (representedExtBoundary L s hs i x) =
        relativeExtBoundary f K E s hs i (α s.X₃ hF₃ i x)) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
