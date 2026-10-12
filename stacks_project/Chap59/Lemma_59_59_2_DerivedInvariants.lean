/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import Mathlib.RepresentationTheory.Invariants
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Definition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import stacks_project.Chap59.Definition_59_57_2_TopRep

/-!
# Derived continuous Galois invariants of discrete modules
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Action.ModuleCat
open CategoryTheory.Functor

noncomputable section

universe u

namespace CategoryTheory.Action.ModuleCat.DiscreteModuleCat

/-- Underived invariants `Γ_G` of a discrete continuous `G`-module, valued in
abelian groups. -/
def invariantsFunctor (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    DiscreteModuleCat ℤ G ⥤ AddCommGrpCat.{u} where
  obj M :=
    (forget₂ (ModuleCat ℤ) AddCommGrpCat).obj
      ((Rep.invariantsFunctor ℤ G).obj ((Rep.ActionToRep ℤ G).obj M.obj))
  map {M N} f :=
    (forget₂ (ModuleCat ℤ) AddCommGrpCat).map
      ((Rep.invariantsFunctor ℤ G).map
        ((Rep.ActionToRep ℤ G).map ((openStabilizer ℤ G).ι.map f)))

/-- The invariants functor on discrete continuous modules is additive. -/
instance invariantsFunctor_additive
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Functor.Additive (invariantsFunctor G) := sorry

/-- Evaluating underived invariants of a discrete continuous `G`-module. -/
theorem invariantsFunctor_obj
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : DiscreteModuleCat ℤ G) :
    (invariantsFunctor G).obj M =
      (forget₂ (TopModuleCat ℤ) (ModuleCat ℤ) ⋙
        forget₂ (ModuleCat ℤ) AddCommGrpCat).obj
        ((TopRep.invariantsFunctor ℤ G).obj (toTopRep G M)) :=
  sorry

/-- Derived invariants `RΓ_G` of discrete continuous `G`-modules, parallel to
`siteAbelianSectionsDerived`. -/
abbrev derivedInvariants (G : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CategoryWithHomology (DiscreteModuleCat ℤ G)]
    [HasDerivedCategory (DiscreteModuleCat ℤ G)]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (invariantsFunctor G))
      (HomologicalComplex.quasiIso (DiscreteModuleCat ℤ G) (ComplexShape.up ℤ))] :
    DerivedCategory (DiscreteModuleCat ℤ G) ⥤
      DerivedCategory AddCommGrpCat.{u} :=
  (RightDerived.Cochain.toDerived (invariantsFunctor G)).totalRightDerived
    DerivedCategory.Q
    (HomologicalComplex.quasiIso (DiscreteModuleCat ℤ G) (ComplexShape.up ℤ))

/-- Evaluating derived invariants on a derived discrete continuous module. -/
theorem derivedInvariants_obj (G : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CategoryWithHomology (DiscreteModuleCat ℤ G)]
    [HasDerivedCategory (DiscreteModuleCat ℤ G)]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (invariantsFunctor G))
      (HomologicalComplex.quasiIso (DiscreteModuleCat ℤ G) (ComplexShape.up ℤ))]
    (K : DerivedCategory (DiscreteModuleCat ℤ G)) :
    (derivedInvariants G).obj K =
      ((RightDerived.Cochain.toDerived (invariantsFunctor G)).totalRightDerived
        DerivedCategory.Q
        (HomologicalComplex.quasiIso (DiscreteModuleCat ℤ G) (ComplexShape.up ℤ))).obj K :=
  sorry

end CategoryTheory.Action.ModuleCat.DiscreteModuleCat
