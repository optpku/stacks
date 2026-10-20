module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Linearity
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.FourierMukai

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Base morphisms induce scalar structures on coherent modules. -/
#check (AlgebraicGeometry.Scheme.baseLinearCoh :
  ∀ {k : Type u} [Field k] {X : Scheme.{u}},
    (X ⟶ Spec (CommRingCat.of k)) → Linear k (RingedSpace.Coh X.toRingedSpace))

/- Relative linearity is a property of functors between coherent-module categories. -/
#check (AlgebraicGeometry.Scheme.LinearOverCoh :
  ∀ {k : Type u} [Field k] {X Y : Scheme.{u}},
    (X ⟶ Spec (CommRingCat.of k)) → (Y ⟶ Spec (CommRingCat.of k)) →
    (RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace) → Prop)

/- Exact linear coherent functors form a full subcategory. -/
#check (AlgebraicGeometry.Scheme.ExactLinearCohFunctor :
  ∀ {k : Type u} [Field k] {X Y : Scheme.{u}},
    (X ⟶ Spec (CommRingCat.of k)) → (Y ⟶ Spec (CommRingCat.of k)) → Type (u + 1))

/- Coherent kernels define functors on coherent modules. -/
#check (AlgebraicGeometry.Scheme.restrictFourierMukai :
  ∀ {k : Type u} [Field k] {X Y : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k)) (y : Y ⟶ Spec (CommRingCat.of k))
    [IsNoetherian X] [QuasiCompact (Limits.pullback.snd x y)]
    [QuasiSeparated (Limits.pullback.snd x y)] (K : (Limits.pullback x y).Modules)
    [AlgebraicGeometry.Scheme.IsCoherentFourierMukaiKernel x y K],
    RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace)
