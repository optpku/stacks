/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Order.WithBotTop
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.ZeroScheme
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.InfinitesimalNeighbourhood
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.Topology.KrullDimension.Local

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

open Hom

namespace InfinitesimalNeighbourhoodCohomology

/-- The cohomology module of the positive infinitesimal neighbourhood `Q_(n+1)` of `Z(s)`. -/
abbrev stage
    {k : Type u} [Field k] (P : SchemeOverField k)
    (L : P.left.Modules) [L.Invertible] (s : L.sections)
    (F : P.left.Modules) (i n : ℕ) : ModuleCat k :=
  Scheme.Hom.cohomology
    (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι n ≫ P.hom)
    ((Scheme.Modules.pullback
      (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι n)).obj F) i

/-- The ambient pushforward view of the positive infinitesimal-neighborhood cohomology stage. -/
abbrev ambientStage
    {k : Type u} [Field k] (P : SchemeOverField k)
    (L : P.left.Modules) [L.Invertible] (s : L.sections)
    (F : P.left.Modules) (i n : ℕ) : ModuleCat k :=
  cohomology P.hom
    ((Scheme.Modules.pushforward
      (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι n)).obj
      ((Scheme.Modules.pullback
        (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι n)).obj F)) i

/-- The neighbourhood cohomology and its ambient pushforward presentation are canonically
isomorphic by the closed-immersion pushforward comparison. -/
theorem stage_isomorphic
    {k : Type u} [Field k] (P : SchemeOverField k)
    (L : P.left.Modules) [L.Invertible] (s : L.sections)
    (F : P.left.Modules) (i n : ℕ) :
    IsIsomorphic (stage P L s F i n) (ambientStage P L s F i n) := sorry

/-- Successive powers of the zero-scheme ideal are ordered by reverse inclusion. -/
theorem ideal_mono
    {k : Type u} [Field k] {P : SchemeOverField k}
    (L : P.left.Modules) [L.Invertible] (s : L.sections) (n : ℕ) :
    InfinitesimalNeighbourhood.ideal (Scheme.zeroIdealSheaf L s).subschemeι (n + 1) ≤
      InfinitesimalNeighbourhood.ideal (Scheme.zeroIdealSheaf L s).subschemeι n := sorry

/-- The canonical scheme morphism from the `n`th positive neighborhood into the next one. -/
def schemeTransition
    {k : Type u} [Field k] (P : SchemeOverField k)
    (L : P.left.Modules) [L.Invertible] (s : L.sections) (n : ℕ) :
    InfinitesimalNeighbourhood.scheme (Scheme.zeroIdealSheaf L s).subschemeι n ⟶
      InfinitesimalNeighbourhood.scheme (Scheme.zeroIdealSheaf L s).subschemeι (n + 1) :=
  Scheme.IdealSheafData.inclusion (ideal_mono L s n)

/-- The canonical neighborhood transition lies over the ambient scheme. -/
theorem schemeTransition_toAmbient
    {k : Type u} [Field k] (P : SchemeOverField k)
    (L : P.left.Modules) [L.Invertible] (s : L.sections) (n : ℕ) :
    schemeTransition P L s n ≫
        InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι (n + 1) =
      InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι n := sorry

/-- The pullback comparison identifying the pullback from the next neighborhood with the
pullback from the current neighborhood. -/
@[no_expose] noncomputable def pullbackIso
    {k : Type u} [Field k] (P : SchemeOverField k)
    (L : P.left.Modules) [L.Invertible] (s : L.sections)
    (F : P.left.Modules) (n : ℕ) :
    (Scheme.Modules.pullback (schemeTransition P L s n)).obj
        ((Scheme.Modules.pullback
          (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι (n + 1))).obj F) ≅
      (Scheme.Modules.pullback
        (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι n)).obj F :=
  (Scheme.Modules.pullbackComp (schemeTransition P L s n)
    (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι (n + 1))).app F ≪≫
    (Scheme.Modules.pullbackCongr
      (schemeTransition_toAmbient P L s n)).app F

/-- Pushing forward the pullback comparison along the neighborhood transition. -/
@[no_expose] noncomputable def pushforwardPullbackIso
    {k : Type u} [Field k] (P : SchemeOverField k)
    (L : P.left.Modules) [L.Invertible] (s : L.sections)
    (F : P.left.Modules) (n : ℕ) :
    (Scheme.Modules.pushforward (schemeTransition P L s n)).obj
        ((Scheme.Modules.pullback (schemeTransition P L s n)).obj
          ((Scheme.Modules.pullback
            (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι (n + 1))).obj F)) ≅
      (Scheme.Modules.pushforward (schemeTransition P L s n)).obj
        ((Scheme.Modules.pullback
          (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι n)).obj F) :=
  (Scheme.Modules.pushforward (schemeTransition P L s n)).mapIso
    (pullbackIso P L s F n)

/-- The sheaf-module map from the next neighborhood module to the pushforward of the current
neighborhood module, obtained from the pullback-pushforward unit and the pullback comparison. -/
@[no_expose] noncomputable def schemeTransitionFMap
    {k : Type u} [Field k] (P : SchemeOverField k)
    (L : P.left.Modules) [L.Invertible] (s : L.sections)
    (F : P.left.Modules) (n : ℕ) :
    (Scheme.Modules.pullback
      (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι (n + 1))).obj F ⟶
      (Scheme.Modules.pushforward (schemeTransition P L s n)).obj
        ((Scheme.Modules.pullback
          (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι n)).obj F) :=
  let g := schemeTransition P L s n
  (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
      ((Scheme.Modules.pullback
        (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι (n + 1))).obj F) ≫
    (pushforwardPullbackIso P L s F n).hom

/-- Pushing a neighborhood transition map forward to the ambient scheme. -/
@[no_expose] noncomputable def pushedSchemeTransitionFMap
    {k : Type u} [Field k] (P : SchemeOverField k)
    (L : P.left.Modules) [L.Invertible] (s : L.sections)
    (F : P.left.Modules) (n : ℕ) :
    (Scheme.Modules.pushforward
      (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι (n + 1))).obj
        ((Scheme.Modules.pullback
          (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι (n + 1))).obj F) ⟶
      (Scheme.Modules.pushforward
        (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι (n + 1))).obj
        ((Scheme.Modules.pushforward (schemeTransition P L s n)).obj
          ((Scheme.Modules.pullback
            (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι n)).obj F)) :=
  (Scheme.Modules.pushforward
    (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι (n + 1))).map
      (schemeTransitionFMap P L s F n)

/-- Composed pushforward along a transition and the next ambient inclusion. -/
@[no_expose] noncomputable def pushforwardCompIso
    {k : Type u} [Field k] (P : SchemeOverField k)
    (L : P.left.Modules) [L.Invertible] (s : L.sections)
    (F : P.left.Modules) (n : ℕ) :
    (Scheme.Modules.pushforward
      (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι (n + 1))).obj
        ((Scheme.Modules.pushforward (schemeTransition P L s n)).obj
          ((Scheme.Modules.pullback
            (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι n)).obj F)) ≅
      (Scheme.Modules.pushforward
        (schemeTransition P L s n ≫
          InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι (n + 1))).obj
        ((Scheme.Modules.pullback
          (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι n)).obj F) :=
  (Scheme.Modules.pushforwardComp (schemeTransition P L s n)
    (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι (n + 1))).app
      ((Scheme.Modules.pullback
        (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι n)).obj F)

/-- Equal ambient inclusions induce the final pushforward comparison. -/
@[no_expose] noncomputable def pushforwardCongrIso
    {k : Type u} [Field k] (P : SchemeOverField k)
    (L : P.left.Modules) [L.Invertible] (s : L.sections)
    (F : P.left.Modules) (n : ℕ) :
    (Scheme.Modules.pushforward
      (schemeTransition P L s n ≫
        InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι (n + 1))).obj
        ((Scheme.Modules.pullback
          (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι n)).obj F) ≅
      (Scheme.Modules.pushforward
        (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι n)).obj
        ((Scheme.Modules.pullback
          (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι n)).obj F) :=
  (Scheme.Modules.pushforwardCongr
    (schemeTransition_toAmbient P L s n)).app
      ((Scheme.Modules.pullback
        (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι n)).obj F)

/-- The neighborhood transition map after pushing both stages to the ambient scheme. -/
@[no_expose] noncomputable def ambientTransitionMap
    {k : Type u} [Field k] (P : SchemeOverField k)
    (L : P.left.Modules) [L.Invertible] (s : L.sections)
    (F : P.left.Modules) (n : ℕ) :
    (Scheme.Modules.pushforward
      (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι (n + 1))).obj
        ((Scheme.Modules.pullback
      (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι (n + 1))).obj F) ⟶
      (Scheme.Modules.pushforward
        (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι n)).obj
        ((Scheme.Modules.pullback
          (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι n)).obj F) :=
  pushedSchemeTransitionFMap P L s F n ≫
    (pushforwardCompIso P L s F n).hom ≫
    (pushforwardCongrIso P L s F n).hom

/-- The canonical cohomology transition from the next positive neighborhood to the current one. -/
noncomputable def transition
    {k : Type u} [Field k] (P : SchemeOverField k)
    (L : P.left.Modules) [L.Invertible] (s : L.sections)
    (F : P.left.Modules) (i n : ℕ) :
    ambientStage P L s F i (n + 1) ⟶ ambientStage P L s F i n :=
  (Scheme.Hom.cohomologyFunctor P.hom i).map
    (ambientTransitionMap P L s F n)

/-- The canonical cohomology restriction from `P` to the `n`th positive neighborhood. -/
noncomputable def restriction
    {k : Type u} [Field k] (P : SchemeOverField k)
    (L : P.left.Modules) [L.Invertible] (s : L.sections)
    (F : P.left.Modules) (i n : ℕ) :
    cohomology P.hom F i ⟶ ambientStage P L s F i n :=
  (Scheme.Hom.cohomologyFunctor P.hom i).map
    ((Scheme.Modules.pullbackPushforwardAdjunction
      (InfinitesimalNeighbourhood.toAmbient (Scheme.zeroIdealSheaf L s).subschemeι n)).unit.app F)

/-- The canonical positive inverse system of neighborhood cohomology modules. -/
noncomputable def system
    {k : Type u} [Field k] (P : SchemeOverField k)
    (L : P.left.Modules) [L.Invertible] (s : L.sections)
    (F : P.left.Modules) (i : ℕ) :
    SequentialInverseSystem (ModuleCat k) :=
  @Functor.ofOpSequence (ModuleCat k) _
    (fun n ↦ ambientStage P L s F i n)
    (fun n ↦ transition P L s F i n)

/-- Every object of the neighbourhood cohomology inverse system is canonically isomorphic to
`Hⁱ(Q_(n+1), F_(n+1))`. -/
theorem system_obj_isomorphic
    {k : Type u} [Field k] (P : SchemeOverField k)
    (L : P.left.Modules) [L.Invertible] (s : L.sections)
    (F : P.left.Modules) (i n : ℕ) :
    IsIsomorphic (stage P L s F i n) ((system P L s F i).obj (op n)) := sorry

/-- The positive neighborhood system has its prescribed cohomology stage at every index. -/
theorem system_obj
    {k : Type u} [Field k] (P : SchemeOverField k)
    (L : P.left.Modules) [L.Invertible] (s : L.sections)
    (F : P.left.Modules) (i n : ℕ) :
    (system P L s F i).obj (op n) = ambientStage P L s F i n := sorry

/-- The successor map of the positive neighborhood system is the canonical transition. -/
theorem system_stepMap
    {k : Type u} [Field k] (P : SchemeOverField k)
    (L : P.left.Modules) [L.Invertible] (s : L.sections)
    (F : P.left.Modules) (i n : ℕ) :
    (system P L s F i).stepMap n = transition P L s F i n := sorry

/-- The ambient restrictions satisfy the successor naturality equation for the positive system. -/
theorem restriction_naturality
    {k : Type u} [Field k] (P : SchemeOverField k)
    (L : P.left.Modules) [L.Invertible] (s : L.sections)
    (F : P.left.Modules) (i n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj (cohomology P.hom F i)).map
        (homOfLE (Nat.le_add_right n 1)).op ≫
      restriction P L s F i n =
    restriction P L s F i (n + 1) ≫
      (system P L s F i).map
        (homOfLE (Nat.le_add_right n 1)).op := sorry

/-- The canonical cone from ambient cohomology to the positive neighborhood system. -/
noncomputable def cone
    {k : Type u} [Field k] (P : SchemeOverField k)
    (L : P.left.Modules) [L.Invertible] (s : L.sections)
    (F : P.left.Modules) (i : ℕ) :
    Cone (system P L s F i) where
  pt := cohomology P.hom F i
  π := NatTrans.ofOpSequence
    (restriction P L s F i)
    (restriction_naturality P L s F i)

/-- The canonical comparison from ambient cohomology to the inverse limit of positive
infinitesimal-neighborhood cohomology. -/
noncomputable def comparison
    {k : Type u} [Field k] (P : SchemeOverField k)
    (L : P.left.Modules) [L.Invertible] (s : L.sections)
    (F : P.left.Modules) (i : ℕ) :
    cohomology P.hom F i ⟶
      limit (system P L s F i) :=
  limit.lift _ (cone P L s F i)

/-- Every limit projection of the comparison is the corresponding ambient restriction. -/
theorem comparison_π
    {k : Type u} [Field k] (P : SchemeOverField k)
    (L : P.left.Modules) [L.Invertible] (s : L.sections)
    (F : P.left.Modules) (i n : ℕ) :
    comparison P L s F i ≫ limit.π (system P L s F i) (op n) =
      restriction P L s F i n := sorry

/-- For a proper scheme over a field and an ample invertible module with a section, the
comparison from coherent-module cohomology to the inverse limit over the positive infinitesimal
neighbourhoods of the zero scheme is an isomorphism in every degree below a depth-plus-closure-
dimension bound away from that zero scheme. -/
theorem comparison_isIso_of_depth
    {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    (L : P.left.Modules) [L.Invertible] [L.IsAmple]
    (s : L.sections) (F : P.left.Modules) [F.IsCoherent]
    (σ : ℤ) (i : ℕ)
    (hdepth : ∀ p : P.left, p ∉ Set.range (Scheme.zeroSchemeι L s) →
      ((WithTop.map Int.ofNat
          (moduleDepth (SchemeOverField.stalkRing P p)
            (RingedSpace.stalkModuleCat F p)) : WithTop ℤ) : EInt) +
        WithBot.map (WithTop.map Int.ofNat)
          (topologicalKrullDim (closure ({p} : Set P.left))) >
        (σ : EInt))
    (his : (i : ℤ) < σ) :
    IsIso (comparison P L s F i) := sorry


end InfinitesimalNeighbourhoodCohomology

end AlgebraicGeometry.Scheme
