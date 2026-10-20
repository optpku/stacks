module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Product
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion
public import stacks_project.Chap42.Definition_42_59_4
public import stacks_project.Chap42.Lemma_42_59_1
public import stacks_project.Chap42.Lemma_42_62_1_IntersectionProduct

/-!
# Graph Gysin maps of morphisms of schemes smooth over a field

This file packages the graph factorization `X ⟶ X ⨯ Y ⟶ Y` of a morphism of schemes
over a field, the associated coborder Gysin class, and the identity-square Gysin
action on total Chow homology.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
open AlgebraicGeometry.Scheme.Modules hiding dual

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
theorem graph_def (f : X ⟶ Y) : graph f = prod.lift (𝟙 X) f := sorry

/-- The graph followed by the second projection recovers the original morphism. -/
theorem graph_comp_snd (f : X ⟶ Y) : graph f ≫ prod.snd = f := sorry

/-- The graph followed by the first projection is the identity of the source. -/
theorem graph_fst (f : X ⟶ Y) : graph f ≫ prod.fst = 𝟙 X := sorry

/-- The graph of a morphism of schemes over a field is an immersion. -/
instance graph_isImmersion (f : X ⟶ Y) : IsImmersion (graph f).left := sorry

/-- The graph of a morphism into a scheme smooth over a field is a regular immersion. -/
instance graph_isRegularImmersion [Smooth Y.hom] (f : X ⟶ Y) :
    IsRegularImmersion (graph f).left := sorry

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
  ClosedSpecialization (fun _ ↦ (0 : ℤ)) X.hom
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
      IsOpenImmersion (graph f).left.coborderRange.ι := sorry

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
            BivariantClass.gysinImmersion (fun _ ↦ 0) (graph f) e D r := sorry

/-- The Gysin class of a morphism of schemes smooth over a field, obtained from the graph
factorization as an immersion followed by a smooth morphism. -/
noncomputable def gysinClass [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
    [IsRegularImmersion (graph f).left]
    (e : Scheme.Modules.dual (normalSheaf (graph f).left) ≅
      conormalSheaf (graph f).left)
    (D : GraphSpecialization f e) (r : ℕ) (t : ℕ)
    [Scheme.Hom.RelativeDimension (prod.snd : X ⨯ Y ⟶ Y).left t] :
    BivariantClass (fun _ ↦ 0) f ((r : ℤ) + (-(t : ℤ))) :=
  BivariantClass.bivariantGysinClassOfFactorization (fun _ ↦ 0) X Y f (X ⨯ Y)
    (graph f) (prod.snd : X ⨯ Y ⟶ Y) inferInstance inferInstance (prod.lift_snd (𝟙 X) f)
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
      BivariantClass.bivariantGysinClassOfFactorization (fun _ ↦ 0) X Y f (X ⨯ Y)
        (graph f) (prod.snd : X ⨯ Y ⟶ Y) inferInstance inferInstance
        (prod.lift_snd (𝟙 X) f) (graphGysinClass f e D r)
        (BivariantClass.flatPullback (fun _ ↦ 0) (prod.snd : X ⨯ Y ⟶ Y) t) := sorry

/-- The Gysin map of a morphism of schemes smooth over a field, acting on total Chow
homology by the identity-square cap of `gysinClass`. -/
noncomputable def gysinMap [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
    [IsRegularImmersion (graph f).left]
    (e : Scheme.Modules.dual (normalSheaf (graph f).left) ≅
      conormalSheaf (graph f).left)
    (D : GraphSpecialization f e) (r : ℕ) (t : ℕ)
    [Scheme.Hom.RelativeDimension (prod.snd : X ⨯ Y ⟶ Y).left t] :
    Total (fun _ ↦ 0) Y →+ Total (fun _ ↦ 0) X :=
  BivariantClass.totalCap (fun _ ↦ 0) (gysinClass f e D r t) (𝟙 X) f (𝟙 Y)
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
          (IsPullback.id_horiz f.left) n alpha) := sorry

end AlgebraicGeometry.ChowGroup
