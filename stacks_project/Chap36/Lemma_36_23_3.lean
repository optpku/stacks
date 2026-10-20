module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.AffineBase
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.RelativeFlat
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 36.23.3: for a finite affine open cover with affine nonempty finite intersections, the
total ordinary Čech complex of a bounded coefficient-linear complex with relatively flat
quasicoherent terms is K-flat over the affine base ring. -/
@[stacks 0FMQ] #check
  (AlgebraicGeometry.Scheme.ModuleCech.total_isKFlat :
    ∀ {A : Type u} [CommRing A] {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
      {ι : Type u} [Finite ι]
      (U : ι → X.Opens) (hU : IsOpenCover U)
      (hAffine : ∀ p : ℕ, ∀ σ : Fin (p + 1) → ι,
        AlgebraicGeometry.IsAffineOpen (⨅ a, U (σ a)))
      (F : ℤ → X.Modules)
      [hQuasicoherent : ∀ n, (F n).IsQuasicoherent]
      [hFlat : ∀ n, SheafOfModules.IsFlatOver (F n) f.toShHom]
      (K : CochainComplex
        (AlgebraicGeometry.Scheme.ModuleCech.relativeSpace f.toShHom).Modules ℤ)
      (termIso : ∀ n, K.X n ≅ SheafOfModules.relativeModule (F n) f.toShHom)
      (hBounded : CochainComplex.bounded _ K),
      ((AlgebraicGeometry.Scheme.ModuleCech.bicomplexOverSpec f U K).total
        (ComplexShape.up ℤ)).IsKFlat)
