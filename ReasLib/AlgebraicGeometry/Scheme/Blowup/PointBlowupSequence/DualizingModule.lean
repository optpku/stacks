module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.FinitePointSequence
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.ReflexiveDeterminant
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.AlgebraicGeometry.Scheme.Module.Dualizing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Relative
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Koszul.PrincipalOpen
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.Determinant

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PointBlowupSequence

/-- The canonical module attached to a finite sequence of point blowups and a module on its
source, obtained by applying the exceptional ideal internal Hom at each stage. -/
noncomputable def canonicalModule {S X : Scheme.{u}} :
    PointBlowupSequence S X → S.Modules → X.Modules
  | .nil _, M => M
  | .cons p b h_blowup tail, M =>
      let I := IdealSheafData.vanishingIdeal (PointClosure.closedSubset p.1)
      let J := I.comap b
      canonicalModule tail (Scheme.Modules.internalHom J.toModule ((Scheme.Modules.pullback b).obj M))

/-- The morphism from a pulled-back module to its internal Hom by the exceptional ideal. -/
noncomputable def exceptionalMap {S X : Scheme.{u}} (b : X ⟶ S)
    (I : S.IdealSheafData) (M : S.Modules) :
    (Scheme.Modules.pullback b).obj M ⟶
      Scheme.Modules.internalHom (I.comap b).toModule ((Scheme.Modules.pullback b).obj M) := by
  let J := I.comap b
  let N := (Scheme.Modules.pullback b).obj M
  exact MonoidalClosed.curry
    ((J.toSubobject.arrow ▷ N) ≫
      ((AlgebraicGeometry.RingedSpace.unitIsoTensorUnit X.toRingedSpace).hom ▷ N) ≫
      (λ_ N).hom)

/-- The canonical comparison from the pullback of a module to the module attached to a finite
sequence of point blowups. -/
noncomputable def canonicalMap {S X : Scheme.{u}} :
    (s : PointBlowupSequence S X) → (M : S.Modules) →
      (Scheme.Modules.pullback s.toSource).obj M ⟶ canonicalModule s M
  | .nil _, M => (Scheme.Modules.pullbackId _).hom.app M
  | .cons p b h_blowup tail, M =>
      let I := IdealSheafData.vanishingIdeal (PointClosure.closedSubset p.1)
      let N := Scheme.Modules.internalHom (I.comap b).toModule
        ((Scheme.Modules.pullback b).obj M)
      let e : (Scheme.Modules.pullback b).obj M ⟶ N := exceptionalMap b I M
      ((Scheme.Modules.pullbackComp tail.toSource b).inv.app M) ≫
        (Scheme.Modules.pullback tail.toSource).map e ≫
        canonicalMap tail N

/-- Under the regular-local differential hypotheses, the recursively constructed canonical module
is normalized as a dualizing module relative to the affine differential determinant. -/
theorem canonicalModule_normalized
    (p : ℕ) (hp : p.Prime) (A₀ A : Type u)
    [CommRing A₀] [CommRing A] [Algebra A₀ A]
    (h_subring : Function.Injective (algebraMap A₀ A))
    [IsRegularLocalRing A] [CharP A p] (h_dimension : ringKrullDim A = 2)
    (r : ℕ) [Module.Free A Ω[A⁄A₀]] [Module.Finite A Ω[A⁄A₀]]
    (h_rank : Module.finrank A Ω[A⁄A₀] = r)
    {X : Scheme.{u}} (s : PointBlowupSequence (Spec (.of A)) X) :
    let S := Spec (.of A)
    let f₀ := Spec.map (CommRingCat.ofHom (algebraMap A₀ A))
    let ωA := (ModuleCat.of A Ω[A⁄A₀]).exteriorPower r
    let ωS := Λ[r] Ω[f₀.toShHom]
    let ωX := canonicalModule s ωS
    let KS := (RingedSpace.ModuleDerived.Koszul.affineDerivedTilde A).obj
      ((ModuleCat.single0 ωA)⟦(2 : ℤ)⟧)
    let KX := ((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧
    ∃ (hX : IsNoetherian X) (hf : IsProper s.toSource),
      @Scheme.IsDualizingModule X hX.toIsLocallyNoetherian ωX ∧
        @Scheme.Hom.NormalizedDualizingComplex.ProperRelativeTo S X inferInstance hX
          s.toSource hf KS KX := sorry

/-- The differential and exceptional-ideal comparisons are isomorphisms on every generic point. -/
theorem genericComparison_spec
    (p : ℕ) (hp : p.Prime) (A₀ A : Type u)
    [CommRing A₀] [CommRing A] [Algebra A₀ A]
    (h_subring : Function.Injective (algebraMap A₀ A))
    [IsRegularLocalRing A] [CharP A p] (h_dimension : ringKrullDim A = 2)
    (r : ℕ) [Module.Free A Ω[A⁄A₀]] [Module.Finite A Ω[A⁄A₀]]
    (h_rank : Module.finrank A Ω[A⁄A₀] = r)
    {X : Scheme.{u}} (s : PointBlowupSequence (Spec (.of A)) X) :
    let f₀ := Spec.map (CommRingCat.ofHom (algebraMap A₀ A))
    let ωS := Λ[r] Ω[f₀.toShHom]
    let d := RelativeDifferentials.reflexiveDeterminantComparison s.toSource f₀ r
    let c := canonicalMap s ωS
    ∀ η : genericPoints X, IsIso (RingedSpace.moduleStalkHom η.1 d) ∧
      IsIso (RingedSpace.moduleStalkHom η.1 c) := sorry

/-- For a regular local surface in positive characteristic, the differential determinant extends
its canonical generic-point comparison to the normalized dualizing module of a point-blowup
sequence. -/
theorem exists_map_toDualizingModule
    (p : ℕ) (hp : p.Prime) (A₀ A : Type u)
    [CommRing A₀] [CommRing A] [Algebra A₀ A]
    (h_subring : Function.Injective (algebraMap A₀ A))
    [IsRegularLocalRing A] [CharP A p] (h_dimension : ringKrullDim A = 2)
    (r : ℕ) [Module.Free A Ω[A⁄A₀]] [Module.Finite A Ω[A⁄A₀]]
    (h_rank : Module.finrank A Ω[A⁄A₀] = r)
    {X : Scheme.{u}} (s : PointBlowupSequence (Spec (.of A)) X) :
    let S := Spec (.of A)
    let f₀ := Spec.map (CommRingCat.ofHom (algebraMap A₀ A))
    let ωA := (ModuleCat.of A Ω[A⁄A₀]).exteriorPower r
    let ωS := Λ[r] Ω[f₀.toShHom]
    let ωX := canonicalModule s ωS
    let ΩrX := Modules.ReflexiveDeterminant.sheaf r Ω[(s.toSource ≫ f₀).toShHom]
    let d := RelativeDifferentials.reflexiveDeterminantComparison s.toSource f₀ r
    let c := canonicalMap s ωS
    ∃ φ : ΩrX ⟶ ωX, ∀ η : genericPoints X,
      RingedSpace.moduleStalkHom η.1 d ≫ RingedSpace.moduleStalkHom η.1 φ =
        RingedSpace.moduleStalkHom η.1 c := sorry

end AlgebraicGeometry.Scheme.PointBlowupSequence
