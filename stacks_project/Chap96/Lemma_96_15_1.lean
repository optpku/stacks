/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Presentation.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.Exactness
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.FppfTensor
import StacksCheckRecall

/-! # Quasi-coherent modules on algebraic stacks -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
  CategoryTheory.Limits CategoryTheory.ObjectProperty AlgebraicGeometry.GroupoidsOver

universe u

/- Lemma 96.15.1 (1): canonical descent to equivariant modules on any presentation. -/
@[stacks 06WV] #check (AlgebraicGeometry.AlgebraicStack.Presentation.equivariantEquivalence :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (P : Presentation X), QCoh X ≌ P.groupoid.QCoh)

/- Lemma 96.15.1 (2): the quasi-coherent module category is abelian. -/
@[stacks 06WV] #check (AlgebraicGeometry.GroupoidsOver.QCoh.instAbelian :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Abelian (QCoh X))

/- Lemma 96.15.1 (3): the inclusion is right exact. -/
@[stacks 06WV] #check (AlgebraicGeometry.GroupoidsOver.QCoh.inclusion_rightExact :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    rightExactFunctor (QCoh X) (RingedSite.ModuleCat.{u} (ringedSite X))
      (QCoh.inclusion X))

/- Lemma 96.15.1 (3): the inclusion is not exact in general, already over Spec Z. -/
@[stacks 06WV] #check (AlgebraicGeometry.GroupoidsOver.QCoh.inclusion_not_exact :
  ¬ exactFunctor
      (QCoh (GroupoidsOver.slice (Over.mk (𝟙 (Spec (CommRingCat.of ℤ))))))
      (RingedSite.ModuleCat (ringedSite _)) (QCoh.inclusion _))

/- Lemma 96.15.1 (4): all universe-compatible colimits exist. -/
@[stacks 06WV] #check (AlgebraicGeometry.GroupoidsOver.QCoh.hasColimitsOfShape :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) (J : Type u) [Category.{u} J],
    HasColimitsOfShape J (QCoh X))

/- Lemma 96.15.1 (4): inclusion preserves the universe-compatible colimits. -/
@[stacks 06WV] #check (AlgebraicGeometry.GroupoidsOver.QCoh.inclusion_preservesColimitsOfShape :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (J : Type u) [Category.{u} J], PreservesColimitsOfShape J (QCoh.inclusion X))

section ColimitComparison

variable {S : Scheme.{u}} {X : GroupoidsOver S} {J : Type u} [Category.{u} J]

/- Lemma 96.15.1 (4): the canonical inclusion comparison identifies the colimits. -/
@[stacks 06WV] #check (CategoryTheory.preservesColimitIso (QCoh.inclusion X) :
  ∀ (K : J ⥤ QCoh X) [PreservesColimit K (QCoh.inclusion X)] [HasColimit K],
    (QCoh.inclusion X).obj (colimit K) ≅ colimit (K ⋙ QCoh.inclusion X))

end ColimitComparison

/- Lemma 96.15.1 (5): the ambient tensor is quasi-coherent. -/
@[stacks 06WV] #check (AlgebraicGeometry.GroupoidsOver.QCoh.Fppf.tensor_isQuasicoherent :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] (F G : QCoh X),
    quasiCoherentModuleProperty X
      ((fromCommFppfModules X).obj (QCoh.Fppf.moduleTensor F G)))

/- Lemma 96.15.1 (5): the quasi-coherent tensor has the prescribed ambient module. -/
@[stacks 06WV] #check (AlgebraicGeometry.GroupoidsOver.QCoh.Fppf.tensor_obj :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] (F G : QCoh X),
    (QCoh.Fppf.tensor F G).obj =
      (fromCommFppfModules X).obj (QCoh.Fppf.moduleTensor F G))

/- Lemma 96.15.1 (5): the ambient tensor comparison is invertible. -/
@[stacks 06WV] #check (AlgebraicGeometry.GroupoidsOver.QCoh.Fppf.tensorComparison_isIso :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] (F G : QCoh X),
    IsIso (QCoh.Fppf.tensorComparison F G))

/- Lemma 96.15.1 (6): internal Hom from a finite locally free module is quasi-coherent. -/
@[stacks 06WV] #check (AlgebraicGeometry.GroupoidsOver.QCoh.Fppf.internalHom :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] (F G : QCoh X)
    [SheafOfModules.IsFiniteLocallyFree F.obj],
    ∃ (H : QCoh X) (ev : QCoh.Fppf.tensor F H ⟶ G),
      IsIso (QCoh.Fppf.internalHomComparison F G H ev))

/- Lemma 96.15.1 (7): quasi-coherent modules are closed under ambient extensions. -/
@[stacks 06WV] #check (AlgebraicGeometry.GroupoidsOver.QCoh.closedUnderExtensions :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    (quasiCoherentModuleProperty X).IsClosedUnderExtensions)

/- Lemma 96.15.1 (7): a short exact sequence with quasi-coherent outer terms has quasi-coherent middle term. -/
@[stacks 06WV] #check (AlgebraicGeometry.GroupoidsOver.QCoh.isQuasicoherent_of_shortExact :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {sc : ShortComplex (RingedSite.ModuleCat.{u} (ringedSite X))},
    sc.ShortExact → quasiCoherentModuleProperty X sc.X₁ →
      quasiCoherentModuleProperty X sc.X₃ → quasiCoherentModuleProperty X sc.X₂)
