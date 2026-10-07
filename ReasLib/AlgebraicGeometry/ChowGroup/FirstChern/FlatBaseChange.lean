module

public import ReasLib.AlgebraicGeometry.ChowGroup.FlatBaseChange
public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.Relative

/-!
# First Chern classes and flat base change

This file records the compatibility of first-Chern-class capping with
dimension-shifted flat base change on Chow groups.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

open Scheme.Modules

/-- Dimension-shifted flat base change commutes with capping by the first Chern class
of an invertible module and its canonical pullback. -/
theorem baseChangePullback_firstChernClassCap
    {S S' : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
    (g : S' ⟶ S) [Flat g] (δ : S → ℤ) [IsDimensionFunction δ]
    (δ' : S' → ℤ) [IsDimensionFunction δ'] (c : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (X : Over S) [LocallyOfFiniteType X.hom]
    (ℒ : X.left.Modules) [Invertible ℒ] (k : ℤ) :
    (@reindex ((Over.pullback g).obj X).left
        (@LocallyOfFiniteType.isLocallyNoetherian _ _ ((Over.pullback g).obj X).hom
          (LocallyOfFiniteType.instOverPullbackObj g X) inferInstance)
        (((Over.pullback g).obj X).hom.relativeDimensionFunction δ') inferInstance
        ((k - 1) + c) (k + c - 1) (sub_add_eq_add_sub k 1 c)).toAddMonoidHom.comp
          ((baseChangePullback g δ δ' c hcompat X.hom (k - 1)).comp
            (firstChernClassCap δ X ℒ k)) =
      (@firstChernClassCap S' inferInstance δ' inferInstance
          ((Over.pullback g).obj X) (LocallyOfFiniteType.instOverPullbackObj g X)
          ((Scheme.Modules.pullback (pullback.fst X.hom g)).obj ℒ)
          (Invertible.pullback (pullback.fst X.hom g) inferInstance)
          (k + c)).comp
        (baseChangePullback g δ δ' c hcompat X.hom k) := sorry

end AlgebraicGeometry.ChowGroup
