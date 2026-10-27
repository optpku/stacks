/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Product
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion
public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin
public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Factorization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Section
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Smooth
public import ReasLib.AlgebraicGeometry.BivariantClass.RegularImmersion
public import ReasLib.AlgebraicGeometry.ChowGroup.Dedekind.ExteriorProduct.Cap
public import ReasLib.AlgebraicGeometry.ChowGroup.ExteriorProduct

/-!
# Graph Gysin maps of morphisms of schemes smooth over a field

This file packages the graph factorization `X ⟶ X ⨯ Y ⟶ Y` of a morphism of schemes
over a field, the associated coborder Gysin class, and the identity-square Gysin
action on total Chow homology.

Deformations to the normal cone are explicit chosen models. Their canonical
construction from the blowup characterization is a library follow-up.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
open AlgebraicGeometry.Scheme.Modules hiding dual
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

variable {k : Type u} [Field k]
variable {X Y : SchemeOverField k}

/-- The graph of a morphism of schemes over a field, as a morphism into the product in
`Over (Spec k)`. -/
noncomputable abbrev graph (f : X ⟶ Y) : X ⟶ X ⨯ Y :=
  prod.lift (𝟙 X) f

/-- The graph morphism is the pairing of the identity with `f`. -/
theorem graph_def (f : X ⟶ Y) : graph f = prod.lift (𝟙 X) f := rfl

/-- The graph followed by the second projection recovers the original morphism. -/
theorem graph_comp_snd (f : X ⟶ Y) : graph f ≫ prod.snd = f := prod.lift_snd _ _

/-- The graph followed by the first projection is the identity of the source. -/
theorem graph_fst (f : X ⟶ Y) : graph f ≫ prod.fst = 𝟙 X := prod.lift_fst _ _

/-- The graph of a morphism of schemes over a field is an immersion. -/
instance graph_isImmersion (f : X ⟶ Y) : IsImmersion (graph f).left :=
  Section.isImmersion (f := (prod.fst : X ⨯ Y ⟶ X).left)
    (by simpa using congrArg (fun g : X ⟶ X ↦ g.left) (graph_fst f))

/-- The graph of a morphism into a scheme smooth over a field is a regular immersion. -/
instance graph_isRegularImmersion [Smooth Y.hom] (f : X ⟶ Y) :
    IsRegularImmersion (graph f).left :=
  Section.isRegularImmersion (f := (prod.fst : X ⨯ Y ⟶ X).left)
    (by simpa using congrArg (fun g : X ⟶ X ↦ g.left) (graph_fst f))

/-- The second projection of a product of schemes over a field is smooth when the first
factor is smooth over the field. -/
instance instSmooth_prodSnd [Smooth X.hom] :
    Smooth (prod.snd : X ⨯ Y ⟶ Y).left := sorry

/-- A morphism of schemes smooth over a field is a local complete intersection morphism. -/
instance instLocalCompleteIntersection_of_smooth
    [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y) :
    LocallyOfType RingHom.IsLocalCompleteIntersection f.left := sorry

/-- Closed-specialization data for the coborder factorization of the graph. -/
abbrev GraphSpecialization [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsRegularImmersion (graph f).left]
    (e : Scheme.Modules.dual (normalSheaf (graph f).left) ≅
      conormalSheaf (graph f).left) :=
  ClosedDeformation X.hom
    ((graph f).left.coborderRange.ι ≫ (X ⨯ Y).hom)
    (graph f).left.liftCoborder
    (factorization_over X.hom (X ⨯ Y).hom (graph f).left (graph f).w
      (graph f).left.liftCoborder (graph f).left.coborderRange.ι
      (graph f).left.liftCoborder_ι)
    (BivariantClass.normalSheafBundle (graph f).left e).toCoborder

/-- `GraphSpecialization` records a closed immersion followed by an open immersion. -/
theorem GraphSpecialization_spec [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsRegularImmersion (graph f).left]
    (e : Scheme.Modules.dual (normalSheaf (graph f).left) ≅
      conormalSheaf (graph f).left)
    (D : GraphSpecialization f e) :
    IsClosedImmersion (graph f).left.liftCoborder ∧
      IsOpenImmersion (graph f).left.coborderRange.ι := ⟨inferInstance, inferInstance⟩

/-- The canonical degree-`r` Gysin class of the graph, obtained from the regular immersion
Gysin class after coborder factorization. -/
noncomputable def graphGysinClass [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsRegularImmersion (graph f).left]
    (e : Scheme.Modules.dual (normalSheaf (graph f).left) ≅
      conormalSheaf (graph f).left)
    (D : GraphSpecialization f e) (r : ℕ) :
    BivariantClass (fun _ ↦ 0) (graph f) (r : ℤ) :=
  BivariantClass.overHom_eq_over (graph f) ▸
    BivariantClass.coborder_factorization (graph f) ▸
      BivariantClass.gysin_open_degree r ▸
        BivariantClass.gysinImmersion (fun _ ↦ 0) (graph f) e D r

/-- `graphGysinClass` is the coborder Gysin class of the graph, transported along the
coborder factorization and the Over-hom comparison. -/
theorem graphGysinClass_def [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsRegularImmersion (graph f).left]
    (e : Scheme.Modules.dual (normalSheaf (graph f).left) ≅
      conormalSheaf (graph f).left)
    (D : GraphSpecialization f e) (r : ℕ) :
    graphGysinClass f e D r =
      BivariantClass.overHom_eq_over (graph f) ▸
        BivariantClass.coborder_factorization (graph f) ▸
          BivariantClass.gysin_open_degree r ▸
            BivariantClass.gysinImmersion (fun _ ↦ 0) (graph f) e D r := rfl

/-- The Gysin class of a morphism of schemes smooth over a field, obtained from the graph
factorization as an immersion followed by a smooth morphism. -/
noncomputable def gysinClass [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
    [IsRegularImmersion (graph f).left]
    (e : Scheme.Modules.dual (normalSheaf (graph f).left) ≅
      conormalSheaf (graph f).left)
    (D : GraphSpecialization f e) (r : ℕ) (t : ℕ)
    [Scheme.Hom.RelativeDimension (prod.snd : X ⨯ Y ⟶ Y).left t] :
    BivariantClass (fun _ ↦ 0) f ((r : ℤ) + (-(t : ℤ))) :=
  graph_comp_snd f ▸
    BivariantClass.comp (fun _ ↦ 0) (graph f) (prod.snd : X ⨯ Y ⟶ Y)
      (graphGysinClass f e D r)
      (BivariantClass.flatPullback (fun _ ↦ 0) (prod.snd : X ⨯ Y ⟶ Y) t)

/-- `gysinClass` is the bivariant Gysin class of the graph factorization. -/
theorem gysinClass_def [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
    [IsRegularImmersion (graph f).left]
    (e : Scheme.Modules.dual (normalSheaf (graph f).left) ≅
      conormalSheaf (graph f).left)
    (D : GraphSpecialization f e) (r : ℕ) (t : ℕ)
    [Scheme.Hom.RelativeDimension (prod.snd : X ⨯ Y ⟶ Y).left t] :
    gysinClass f e D r t =
      graph_comp_snd f ▸
        BivariantClass.comp (fun _ ↦ 0) (graph f) (prod.snd : X ⨯ Y ⟶ Y)
          (graphGysinClass f e D r)
          (BivariantClass.flatPullback (fun _ ↦ 0) (prod.snd : X ⨯ Y ⟶ Y) t) := rfl

/-- The Gysin map of a morphism of schemes smooth over a field, acting on total Chow
homology by the identity-square cap of `gysinClass`. -/
noncomputable def gysinMap [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
    [IsRegularImmersion (graph f).left]
    (e : Scheme.Modules.dual (normalSheaf (graph f).left) ≅
      conormalSheaf (graph f).left)
    (D : GraphSpecialization f e) (r : ℕ) (t : ℕ)
    [Scheme.Hom.RelativeDimension (prod.snd : X ⨯ Y ⟶ Y).left t] :
    Total (fun _ ↦ 0) Y →+ Total (fun _ ↦ 0) X :=
  Dedekind.Total.cap (fun _ ↦ 0) (gysinClass f e D r t) (𝟙 X) f (𝟙 Y)
    (IsPullback.id_horiz f.left)

/-- Evaluation of `gysinMap` on a homogeneous class is the corresponding identity-square
cap in shifted degree. -/
theorem gysinMap_apply [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
    [IsRegularImmersion (graph f).left]
    (e : Scheme.Modules.dual (normalSheaf (graph f).left) ≅
      conormalSheaf (graph f).left)
    (D : GraphSpecialization f e) (r : ℕ) (t : ℕ)
    [Scheme.Hom.RelativeDimension (prod.snd : X ⨯ Y ⟶ Y).left t]
    (n : ℤ) (alpha : RelativeChow (fun _ ↦ 0) Y n) :
    gysinMap f e D r t (DirectSum.of _ n alpha) =
      DirectSum.of (fun d : ℤ ↦ RelativeChow (fun _ ↦ 0) X d)
        (n - ((r : ℤ) + (-(t : ℤ))))
        ((gysinClass f e D r t).cap (𝟙 X) f (𝟙 Y)
          (IsPullback.id_horiz f.left) n alpha) :=
  Dedekind.Total.cap_of (fun _ ↦ 0) (gysinClass f e D r t)
    (𝟙 X) f (𝟙 Y) (IsPullback.id_horiz f.left) n alpha

/-- A chosen deformation of the closed coborder factor of the graph, with its
canonical normal bundle and locally varying rank. -/
abbrev GraphSpecializationOfRankLoci [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y) :=
  BivariantClass.Gysin.NormalSpecializationOfRankLoci (graph f)

/-- The integer-degree Gysin coefficient of a morphism between smooth schemes is the
normal Gysin coefficient of its graph followed by smooth projection pullback. -/
def gysinClassDegree [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
    (D : GraphSpecializationOfRankLoci f) (p : ℤ) : BivariantClass (fun _ ↦ 0) f p :=
  BivariantClass.Gysin.factorizationClassDegree (fun _ ↦ 0) f (graph f)
    (prod.snd : X ⨯ Y ⟶ Y) (graph_comp_snd f)
    (bidualityIsoOfRankLoci (graph f).left) D p

/-- On each common normal-rank and projection-dimension locus, the Gysin coefficient
is the corresponding geometric factorization coefficient. -/
theorem gysinClassDegree_component [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
    (D : GraphSpecializationOfRankLoci f) (p : ℤ) (rt : ℕ × ℕ) :
    BivariantClass.ComponentRestriction.restrict (fun _ ↦ 0) f p
      (BivariantClass.Gysin.factorizationRankLoci (graph f) (prod.snd : X ⨯ Y ⟶ Y)
        (bidualityIsoOfRankLoci (graph f).left) rt) ⊤ (by simp)
      (gysinClassDegree f D p) =
    BivariantClass.Gysin.factorizationComponentDegree (fun _ ↦ 0) f (graph f)
      (prod.snd : X ⨯ Y ⟶ Y) (graph_comp_snd f)
      (bidualityIsoOfRankLoci (graph f).left) D p rt :=
  BivariantClass.Gysin.factorizationClassDegree_component (fun _ ↦ 0) f (graph f)
    (prod.snd : X ⨯ Y ⟶ Y) (graph_comp_snd f)
    (bidualityIsoOfRankLoci (graph f).left) D p rt

/-- Gysin coefficients do not depend on the chosen graph deformation. -/
theorem gysinClassDegree_independent [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
    (D D' : GraphSpecializationOfRankLoci f) (p : ℤ) :
    gysinClassDegree f D p = gysinClassDegree f D' p :=
  congrFun (BivariantClass.gysin_eq_of_factorization (fun _ ↦ 0) f
    (graph f) (prod.snd : X ⨯ Y ⟶ Y) (graph_comp_snd f)
    (bidualityIsoOfRankLoci (graph f).left) D
    (graph f) (prod.snd : X ⨯ Y ⟶ Y) (graph_comp_snd f)
    (bidualityIsoOfRankLoci (graph f).left) D') p

/-- For a smooth source of dimension `d`, the total Gysin action is the finite sum of
its graph coefficients with output degrees from zero to `d`. -/
def gysinMapOfDimension [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
    (D : GraphSpecializationOfRankLoci f) (d : ℕ) [RelativeDimension X.hom d] :
    Total (fun _ ↦ 0) Y →+ Total (fun _ ↦ 0) X :=
  DirectSum.toAddMonoid fun n ↦
    ∑ j ∈ Finset.range (d + 1),
      (Dedekind.Total.cap (fun _ ↦ 0) (gysinClassDegree f D (n - (j : ℤ)))
        (𝟙 X) f (𝟙 Y) (IsPullback.id_horiz f.left)).comp (DirectSum.of _ n)

/-- The action on a homogeneous input is the finite sum of graph caps in the allowed
output dimensions. -/
theorem gysinMapOfDimension_of [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
    (D : GraphSpecializationOfRankLoci f) (d : ℕ) [RelativeDimension X.hom d]
    (n : ℤ) (alpha : RelativeChow (fun _ ↦ 0) Y n) :
    gysinMapOfDimension f D d (DirectSum.of _ n alpha) =
      ∑ j ∈ Finset.range (d + 1),
        Dedekind.Total.cap (fun _ ↦ 0) (gysinClassDegree f D (n - (j : ℤ)))
          (𝟙 X) f (𝟙 Y) (IsPullback.id_horiz f.left) (DirectSum.of _ n alpha) := by
  simp only [gysinMapOfDimension, DirectSum.toAddMonoid_of, AddMonoidHom.finsetSum_apply,
    AddMonoidHom.comp_apply]

/-- The finite total Gysin action is independent of the graph deformation model. -/
theorem gysinMapOfDimension_independent [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
    (D D' : GraphSpecializationOfRankLoci f) (d : ℕ) [RelativeDimension X.hom d] :
    gysinMapOfDimension f D d = gysinMapOfDimension f D' d := by
  simp only [gysinMapOfDimension, gysinClassDegree_independent f D D']

/-- Every integer-degree coefficient of the finite total Gysin action is the identity
square cap of the corresponding graph coefficient, including outside the dimension range. -/
theorem gysinMapOfDimension_cap [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
    (D : GraphSpecializationOfRankLoci f) (d : ℕ) [RelativeDimension X.hom d]
    (n p : ℤ) (alpha : RelativeChow (fun _ ↦ 0) Y n) :
    (gysinMapOfDimension f D d (DirectSum.of _ n alpha)) (n - p) =
      (gysinClassDegree f D p).cap (𝟙 X) f (𝟙 Y)
        (IsPullback.id_horiz f.left) n alpha := sorry

/-- With constant normal rank and projection dimension, the finite total action agrees
with the fixed-degree graph Gysin action. -/
theorem gysinMapOfDimension_eq_legacy [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
    (D : GraphSpecializationOfRankLoci f) (d : ℕ) [RelativeDimension X.hom d]
    (e : Scheme.Modules.dual (normalSheaf (graph f).left) ≅
      conormalSheaf (graph f).left)
    (D' : GraphSpecialization f e) (r t : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (graph f).left)]
    [RelativeDimension (prod.snd : X ⨯ Y ⟶ Y).left t] :
    gysinMapOfDimension f D d = gysinMap f e D' r t := sorry

end AlgebraicGeometry.ChowGroup

namespace AlgebraicGeometry.BivariantClass

/-- Every morphism between schemes smooth over a field admits an immersion–smooth
factorization and hence has a Gysin map. -/
theorem hasGysinMap_of_smooth {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y) : HasGysinMap f :=
  (HasGysinMap.iff_exists f).mpr ⟨X ⨯ Y, ChowGroup.graph f, prod.snd,
    inferInstance, inferInstance, ChowGroup.graph_comp_snd f⟩

end AlgebraicGeometry.BivariantClass
