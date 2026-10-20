module

public import ReasLib.RingTheory.RingHom.SquareZero.Obstruction
import StacksCheckRecall

/-!
# Obstruction and torsor of fillers of a two-solution square-zero diagram

Given a commutative diagram whose front and back faces are solutions of the
relative square-zero problem, the obstruction class vanishes exactly when a
filler exists, and the fillers form a principal homogeneous space.
-/

@[expose] public section

universe u

/- Lemma 91.2.1 (1) -/
@[stacks 08S5] #check (RingHom.SquareZeroExtension.mapObstruction_eq_zero_iff :
  ∀ {A₁' A₁ B₁ N₁ A₂' A₂ B₂ N₂ : Type u} [CommRing A₁'] [CommRing A₁]
    [CommRing B₁] [Algebra A₁ B₁] [CommRing A₂'] [CommRing A₂] [CommRing B₂]
    [Algebra A₂ B₂] [AddCommGroup N₁] [Module B₁ N₁] [Module A₁ N₁]
    [IsScalarTower A₁ B₁ N₁] [AddCommGroup N₂] [Module B₂ N₂] [Module A₂ N₂]
    [IsScalarTower A₂ B₂ N₂] {π₁ : A₁' →+* A₁} [π₁.IsSquareZeroExtension]
    {π₂ : A₂' →+* A₂} [π₂.IsSquareZeroExtension]
    {c₁ : RingHom.SquareZeroExtension.KernelModule π₁ →ₗ[A₁] N₁}
    {c₂ : RingHom.SquareZeroExtension.KernelModule π₂ →ₗ[A₂] N₂}
    {S₁ : RingHom.SquareZeroExtension.Solution π₁ c₁}
    {S₂ : RingHom.SquareZeroExtension.Solution π₂ c₂}
    (D : RingHom.SquareZeroExtension.RelativeDiagram S₁ S₂),
      RingHom.SquareZeroExtension.RelativeDiagram.mapObstruction D = 0 ↔
        Nonempty (RingHom.SquareZeroExtension.FittingMap D))

/- Lemma 91.2.1 (2) -/
@[stacks 08S5] #check (RingHom.SquareZeroExtension.fittingMap_principalHomogeneous :
  ∀ {A₁' A₁ B₁ N₁ A₂' A₂ B₂ N₂ : Type u} [CommRing A₁'] [CommRing A₁]
    [CommRing B₁] [Algebra A₁ B₁] [CommRing A₂'] [CommRing A₂] [CommRing B₂]
    [Algebra A₂ B₂] [AddCommGroup N₁] [Module B₁ N₁] [Module A₁ N₁]
    [IsScalarTower A₁ B₁ N₁] [AddCommGroup N₂] [Module B₂ N₂] [Module A₂ N₂]
    [IsScalarTower A₂ B₂ N₂] {π₁ : A₁' →+* A₁} [π₁.IsSquareZeroExtension]
    {π₂ : A₂' →+* A₂} [π₂.IsSquareZeroExtension]
    {c₁ : RingHom.SquareZeroExtension.KernelModule π₁ →ₗ[A₁] N₁}
    {c₂ : RingHom.SquareZeroExtension.KernelModule π₂ →ₗ[A₂] N₂}
    {S₁ : RingHom.SquareZeroExtension.Solution π₁ c₁}
    {S₂ : RingHom.SquareZeroExtension.Solution π₂ c₂}
    (D : RingHom.SquareZeroExtension.RelativeDiagram S₁ S₂)
    (φ φ' : RingHom.SquareZeroExtension.FittingMap D),
    ∃! α : RingHom.SquareZeroExtension.RelativeDiagram.Differentials D,
      RingHom.SquareZeroExtension.FittingMap.perturb D α φ = φ')
