/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Triangulated
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent.Transitivity
public import stacks_project.Chap91.Lemma_91_7_1_Obstruction

/-!
# Functoriality of derived Ext¹ along ringed-space pullback and coefficient maps

The maps `L(g)^*` and `L(g)^* F[0] ⟶ G[0]` induced by `g : Y ⟶ X` and an
`𝒪_Y`-linear coefficient map `c` act on `Ext⁽1⁾(Q NL[f], Q(F[0]))`, while
precomposition along `L(g)^* NL[f] ⟶ NL[g ≫ f]` acts on
`Ext⁽1⁾(Q NL[g ≫ f], Q(G[0]))`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening

variable {S X Y : RingedSpace.{u}}

/-- Underived comparison `g^* NL[f] ⟶ NL[g ≫ f]` along a composable pair of
morphisms of ringed spaces. -/
def naiveCotangentCochainComparison (f : X ⟶ S) (g : Y ⟶ X) :
    ((g^*).mapHomologicalComplex (ComplexShape.up ℤ)).obj NL[f] ⟶ NL[g ≫ f] :=
  (NaiveCotangent.Pullback.chosenComplexIso g f).hom ≫ NaiveCotangent.left g f

/-- `naiveCotangentCochainComparison` is the chosen pullback comparison of
`g^* NL[f]` followed by the transitivity map to `NL[g ≫ f]`. -/
theorem naiveCotangentCochainComparison_spec (f : X ⟶ S) (g : Y ⟶ X) :
    naiveCotangentCochainComparison f g =
      (NaiveCotangent.Pullback.chosenComplexIso g f).hom ≫
        NaiveCotangent.left g f := sorry

/-- Derived-to-underived comparison `L(g)^* NL[f] ⟶ NL[g ≫ f]`. -/
def naiveCotangentComparison (f : X ⟶ S) (g : Y ⟶ X) :
    (modulePullbackDerived g).obj ((moduleQ X).obj NL[f]) ⟶
      (moduleQ Y).obj NL[g ≫ f] :=
  (Functor.LeftDerived.Homotopy.cochainCounit (g^*)).app NL[f] ≫
    (moduleQ Y).map (naiveCotangentCochainComparison f g)

/-- `naiveCotangentComparison` is the cochain counit of module pullback at
`NL[f]`, followed by `moduleQ.map` of `naiveCotangentCochainComparison`. -/
theorem naiveCotangentComparison_spec (f : X ⟶ S) (g : Y ⟶ X) :
    naiveCotangentComparison f g =
      (Functor.LeftDerived.Homotopy.cochainCounit (g^*)).app NL[f] ≫
        (moduleQ Y).map (naiveCotangentCochainComparison f g) := sorry

variable {F : X.Modules} {G : Y.Modules}

/-- Derived-to-underived comparison `L(g)^* F[0] ⟶ G[0]` along `c : g^* F ⟶ G`. -/
def coeffDerived {g : Y ⟶ X} (c : (g^*).obj F ⟶ G) :
    (modulePullbackDerived g).obj
        ((moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj F)) ⟶
      (moduleQ Y).obj ((CochainComplex.singleFunctor Y.Modules 0).obj G) :=
  (Functor.LeftDerived.Homotopy.cochainCounit (g^*)).app
      ((CochainComplex.singleFunctor X.Modules 0).obj F) ≫
    (moduleQ Y).map
      ((HomologicalComplex.singleMapHomologicalComplex (g^*)
            (ComplexShape.up ℤ) (0 : ℤ)).hom.app F ≫
        (CochainComplex.singleFunctor Y.Modules 0).map c)

/-- `coeffDerived` is the cochain counit at `F[0]`, followed by `moduleQ.map` of
the single-complex comparison along `c`. -/
theorem coeffDerived_spec {g : Y ⟶ X} (c : (g^*).obj F ⟶ G) :
    coeffDerived c =
      (Functor.LeftDerived.Homotopy.cochainCounit (g^*)).app
          ((CochainComplex.singleFunctor X.Modules 0).obj F) ≫
        (moduleQ Y).map
          ((HomologicalComplex.singleMapHomologicalComplex (g^*)
                (ComplexShape.up ℤ) (0 : ℤ)).hom.app F ≫
            (CochainComplex.singleFunctor Y.Modules 0).map c) := sorry

/-- Pullback `Ext⁽1⁾(Q NL[f], Q F[0]) → Ext⁽1⁾(L(g)^* NL[f], L(g)^* F[0])`
along `L(g)^*`, compared by `commShift 1`. -/
def extOne_pullback {f : X ⟶ S} (g : Y ⟶ X)
    (ξ :
      Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f],
        (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj F))) :
    Ext⁽(1 : ℤ)⁾((modulePullbackDerived g).obj ((moduleQ X).obj NL[f]),
      (modulePullbackDerived g).obj
        ((moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj F))) :=
  (modulePullbackDerived g).map ξ ≫
    ((modulePullbackDerived.commShift g).commShiftIso (1 : ℤ)).hom.app
      ((moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj F))

/-- `extOne_pullback` is `L(g)^*` on the Ext class, compared by `commShiftIso 1`. -/
theorem extOne_pullback_apply {f : X ⟶ S} (g : Y ⟶ X)
    (ξ :
      Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f],
        (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj F))) :
    extOne_pullback g ξ =
      (modulePullbackDerived g).map ξ ≫
        ((modulePullbackDerived.commShift g).commShiftIso (1 : ℤ)).hom.app
          ((moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj F)) :=
  sorry

/-- Postcomposition `Ext⁽1⁾(L(g)^* NL[f], L(g)^* F[0]) → Ext⁽1⁾(L(g)^* NL[f], Q G[0])`
along `coeffDerived c`. -/
def extOne_postcomp {f : X ⟶ S} {g : Y ⟶ X} (c : (g^*).obj F ⟶ G)
    (ξ :
      Ext⁽(1 : ℤ)⁾((modulePullbackDerived g).obj ((moduleQ X).obj NL[f]),
        (modulePullbackDerived g).obj
          ((moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj F)))) :
    Ext⁽(1 : ℤ)⁾((modulePullbackDerived g).obj ((moduleQ X).obj NL[f]),
      (moduleQ Y).obj ((CochainComplex.singleFunctor Y.Modules 0).obj G)) :=
  ShiftedHom.comp ξ (ShiftedHom.mk₀ (0 : ℤ) rfl (coeffDerived c)) (zero_add (1 : ℤ))

/-- The composite `Ext⁽1⁾(Q NL[f], Q F[0]) → Ext⁽1⁾(L(g)^* NL[f], Q G[0])` sending
ξ along `L(g)^*` and then along `L(g)^* F ⟶ g^* F ⟶ G`. -/
def extOne_map {f : X ⟶ S} {g : Y ⟶ X} (c : (g^*).obj F ⟶ G)
    (ξ :
      Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f],
        (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj F))) :
    Ext⁽(1 : ℤ)⁾((modulePullbackDerived g).obj ((moduleQ X).obj NL[f]),
      (moduleQ Y).obj ((CochainComplex.singleFunctor Y.Modules 0).obj G)) :=
  extOne_postcomp c (extOne_pullback g ξ)

/-- `extOne_map` is pullback along `L(g)^*` followed by postcomposition along `c`. -/
theorem extOne_map_spec {f : X ⟶ S} {g : Y ⟶ X} (c : (g^*).obj F ⟶ G)
    (ξ :
      Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f],
        (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj F))) :
    extOne_map c ξ = extOne_postcomp c (extOne_pullback g ξ) := sorry

/-- The zero Ext¹ class is sent to zero under `extOne_map`. -/
theorem extOne_map_zero {f : X ⟶ S} {g : Y ⟶ X} (c : (g^*).obj F ⟶ G) :
    extOne_map c
      (0 :
        Ext⁽(1 : ℤ)⁾((moduleQ X).obj NL[f],
          (moduleQ X).obj ((CochainComplex.singleFunctor X.Modules 0).obj F))) = 0 :=
  sorry

/-- Precomposition `Ext⁽1⁾(Q NL[g ≫ f], Q G[0]) → Ext⁽1⁾(L(g)^* NL[f], Q G[0])`
along `naiveCotangentComparison`. -/
def extOne_comap (f : X ⟶ S) (g : Y ⟶ X)
    (ζ :
      Ext⁽(1 : ℤ)⁾((moduleQ Y).obj NL[g ≫ f],
        (moduleQ Y).obj ((CochainComplex.singleFunctor Y.Modules 0).obj G))) :
    Ext⁽(1 : ℤ)⁾((modulePullbackDerived g).obj ((moduleQ X).obj NL[f]),
      (moduleQ Y).obj ((CochainComplex.singleFunctor Y.Modules 0).obj G)) :=
  ShiftedHom.comp
    (ShiftedHom.mk₀ (0 : ℤ) rfl (naiveCotangentComparison f g)) ζ (add_zero (1 : ℤ))

/-- `extOne_comap` is precomposition along `naiveCotangentComparison`. -/
theorem extOne_comap_spec (f : X ⟶ S) (g : Y ⟶ X)
    (ζ :
      Ext⁽(1 : ℤ)⁾((moduleQ Y).obj NL[g ≫ f],
        (moduleQ Y).obj ((CochainComplex.singleFunctor Y.Modules 0).obj G))) :
    extOne_comap f g ζ =
      ShiftedHom.comp
        (ShiftedHom.mk₀ (0 : ℤ) rfl (naiveCotangentComparison f g)) ζ
        (add_zero (1 : ℤ)) := sorry

/-- The zero Ext¹ class is sent to zero under `extOne_comap`. -/
theorem extOne_comap_zero (f : X ⟶ S) (g : Y ⟶ X) :
    extOne_comap f g
      (0 :
        Ext⁽(1 : ℤ)⁾((moduleQ Y).obj NL[g ≫ f],
          (moduleQ Y).obj ((CochainComplex.singleFunctor Y.Modules 0).obj G))) = 0 :=
  sorry

end AlgebraicGeometry.RingedSpace.Thickening
