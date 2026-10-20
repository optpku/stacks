/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import stacks_project.Chap67.Lemma_67_19_5_UniversallyInjective
public import stacks_project.Chap68.Lemma_68_17_4_Relative
public import stacks_project.Chap76.Example_76_3_3
public import stacks_project.Chap76.Remark_76_3_5_WeaklyRadicial
import StacksCheckRecall

/-!
# Weakly radicial morphisms of algebraic spaces

Remark 76.3.5 records the weaker fibrewise condition that every field-valued
fibre has singleton points space and a purely inseparable monomorphism from a
field spectrum, together with the algebraically closed points consequence, the
base change of Example 76.3.3, and the property (β) analogue of Lemma 76.3.4.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Remark 76.3.5 (1): a morphism `f : X ⟶ Y` of algebraic spaces is weakly
radicial if for every field-valued point `Spec(K) ⟶ Y` the space
`|Spec(K) ×_Y X|` is a singleton, there exists a monomorphism
`Spec(L) ⟶ Spec(K) ×_Y X`, and `K ⊆ L` is purely inseparable. -/
@[stacks 049E]
#check WeaklyRadicial

namespace AlgebraicGeometry.AlgebraicSpace.WeaklyRadicial

/-- Remark 76.3.5 (2): a surjective weakly radicial morphism of algebraic spaces
is surjective on `k`-points for every algebraically closed field `k`. -/
@[stacks 049E]
theorem surjectiveOnAlgClosedFieldPoints {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [WeaklyRadicial f] [Surjective f] (k : Type u) [Field k]
    [IsAlgClosed k] (σ : Spec (.of k) ⟶ S) :
    Function.Surjective (fun x : ofOver (Over.mk σ) ⟶ X ↦ x ≫ f) :=
  sorry

/-- Remark 76.3.5 (5): a universally injective morphism of algebraic spaces with
property (β) is weakly radicial. -/
@[stacks 049E]
instance of_universallyInjective_of_propertyBeta {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [UniversallyInjective f]
    [PropertyBeta f] : WeaklyRadicial f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.WeaklyRadicial

namespace AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient

/-- The triangle witnessing that `Spec L ⟶ Spec algebraicQ` is a morphism over
`Spec ℚ`. -/
theorem specToCover_w (L : Type) [Field L] [Algebra algebraicQ L] :
    FieldExtension.specMap algebraicQ L ≫ cover.hom =
      (Over.mk (FieldExtension.specMap algebraicQ L ≫ cover.hom)).hom :=
  sorry

/-- The structure morphism of `Spec L` over `Spec algebraicQ`, as a morphism of
schemes over `Spec ℚ`. -/
def specToCover (L : Type) [Field L] [Algebra algebraicQ L] :
    Over.mk (FieldExtension.specMap algebraicQ L ≫ cover.hom) ⟶ cover :=
  Over.homMk (FieldExtension.specMap algebraicQ L) (specToCover_w L)

/-- `specToCover L` is `Over.homMk` of `FieldExtension.specMap algebraicQ L`. -/
theorem specToCover_eq (L : Type) [Field L] [Algebra algebraicQ L] :
    specToCover L =
      Over.homMk (FieldExtension.specMap algebraicQ L) (specToCover_w L) :=
  sorry

/-- The sheaf fibre product `X ×_{Spec ℚ} Spec algebraicQ` of `toSpec` along the
atlas `Spec algebraicQ ⟶ Spec ℚ`. -/
abbrev toSpec_pullback : Sheaf (Scheme.fppfTopology.over base) (Type 1) :=
  pullback toSpec ((Scheme.fppfTopology.over base).uliftYoneda.{1}.map coverToBase)

/-- `toSpec_pullback` is the pullback of `toSpec` along the Yoneda image of
`coverToBase`. -/
theorem toSpec_pullback_eq :
    toSpec_pullback =
      pullback toSpec
        ((Scheme.fppfTopology.over base).uliftYoneda.{1}.map coverToBase) :=
  sorry

/-- The base change `X_{algebraicQ} ⟶ Spec algebraicQ` of `toSpec` along
`Spec algebraicQ ⟶ Spec ℚ`. -/
def toSpec_baseChange :
    toSpec_pullback ⟶
      (Scheme.fppfTopology.over base).uliftYoneda.{1}.obj cover :=
  pullback.snd toSpec
    ((Scheme.fppfTopology.over base).uliftYoneda.{1}.map coverToBase)

/-- `toSpec_baseChange` is `pullback.snd` of `toSpec` along the Yoneda image of
`coverToBase`. -/
theorem toSpec_baseChange_eq :
    toSpec_baseChange =
      pullback.snd toSpec
        ((Scheme.fppfTopology.over base).uliftYoneda.{1}.map coverToBase) :=
  sorry

/-- The triangle witnessing that `Spec L ⟶ Spec K` is a morphism over `Spec ℚ`. -/
theorem specOver_w (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
    [Algebra K L] :
    FieldExtension.specMap K L ≫ FieldExtension.specMap ℚ K =
      FieldExtension.specMap ℚ L :=
  sorry

/-- The structure morphism of `Spec L` over `Spec K`, as a morphism of schemes
over `Spec ℚ`. -/
def specOver (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
    [Algebra K L] :
    Over.mk (FieldExtension.specMap ℚ L) ⟶
      Over.mk (FieldExtension.specMap ℚ K) :=
  Over.homMk (FieldExtension.specMap K L) (specOver_w K L)

/-- `specOver K L` is `Over.homMk` of `FieldExtension.specMap K L`. -/
theorem specOver_eq (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
    [Algebra K L] :
    specOver K L =
      Over.homMk (FieldExtension.specMap K L) (specOver_w K L) :=
  sorry

/-- A field-valued point of an fppf sheaf over `Spec ℚ` is a morphism from
`Spec(K)` over `Spec ℚ`. -/
structure SheafFieldValuedPoint
    (F : Sheaf (Scheme.fppfTopology.over base) (Type 1)) where
  /-- The source field. -/
  K : Type
  /-- The field structure on the source. -/
  [field : Field K]
  /-- The structure morphism of `Spec(K)` over `Spec ℚ`. -/
  structureHom : Spec (.of K) ⟶ base
  /-- The morphism `Spec(K) ⟶ F` of fppf sheaves over `Spec ℚ`. -/
  hom :
    (Scheme.fppfTopology.over base).uliftYoneda.{1}.obj (Over.mk structureHom) ⟶ F

namespace SheafFieldValuedPoint

attribute [instance] field

/-- Construct a field-valued point of an fppf sheaf over `Spec ℚ`. -/
def of {F : Sheaf (Scheme.fppfTopology.over base) (Type 1)} (K : Type) [Field K]
    (structureHom : Spec (.of K) ⟶ base)
    (hom :
      (Scheme.fppfTopology.over base).uliftYoneda.{1}.obj (Over.mk structureHom) ⟶
        F) :
    SheafFieldValuedPoint F where
  K := K
  structureHom := structureHom
  hom := hom

/-- Postcompose a field-valued point with a morphism of fppf sheaves over
`Spec ℚ`. -/
def map {F G : Sheaf (Scheme.fppfTopology.over base) (Type 1)}
    (p : SheafFieldValuedPoint F) (f : F ⟶ G) : SheafFieldValuedPoint G where
  K := p.K
  field := p.field
  structureHom := p.structureHom
  hom := p.hom ≫ f

/-- Field-valued points of an fppf sheaf over `Spec ℚ` are equivalent when they
admit a common field-valued extension, as for `FieldValuedPoint.Equivalent`. -/
def Equivalent {F : Sheaf (Scheme.fppfTopology.over base) (Type 1)}
    (p q : SheafFieldValuedPoint F) : Prop :=
  ∃ (L : Type) (_ : Field L) (hL : Spec (.of L) ⟶ base)
    (r :
      (Scheme.fppfTopology.over base).uliftYoneda.{1}.obj (Over.mk hL) ⟶ F)
    (i : Spec (.of L) ⟶ Spec (.of p.K)) (j : Spec (.of L) ⟶ Spec (.of q.K))
    (hi : i ≫ p.structureHom = hL) (hj : j ≫ q.structureHom = hL),
    (Scheme.fppfTopology.over base).uliftYoneda.{1}.map (Over.homMk i hi) ≫
        p.hom = r ∧
      (Scheme.fppfTopology.over base).uliftYoneda.{1}.map (Over.homMk j hj) ≫
          q.hom = r

/-- Equivalence of field-valued points of an fppf sheaf is reflexive. -/
theorem Equivalent.refl {F : Sheaf (Scheme.fppfTopology.over base) (Type 1)}
    (p : SheafFieldValuedPoint F) : Equivalent p p :=
  sorry

/-- Equivalence of field-valued points is preserved by postcomposition. -/
theorem Equivalent.map {F G : Sheaf (Scheme.fppfTopology.over base) (Type 1)}
    {p q : SheafFieldValuedPoint F} (h : Equivalent p q) (f : F ⟶ G) :
    Equivalent (p.map f) (q.map f) :=
  sorry

/-- The setoid of field-valued points of an fppf sheaf over `Spec ℚ`. -/
def equivalentSetoid (F : Sheaf (Scheme.fppfTopology.over base) (Type 1)) :
    Setoid (SheafFieldValuedPoint F) where
  r := Equivalent
  iseqv := sorry

/-- The setoid relation is the common-extension equivalence. -/
theorem equivalentSetoid_rel_iff
    {F : Sheaf (Scheme.fppfTopology.over base) (Type 1)}
    (p q : SheafFieldValuedPoint F) :
    equivalentSetoid F p q ↔ Equivalent p q :=
  sorry

end SheafFieldValuedPoint

/-- The space of points of an fppf sheaf over `Spec ℚ`, as equivalence classes of
morphisms from spectra of fields. -/
def SheafPoints (F : Sheaf (Scheme.fppfTopology.over base) (Type 1)) :=
  Quotient (SheafFieldValuedPoint.equivalentSetoid F)

namespace SheafPoints

/-- The class of a field-valued point of an fppf sheaf over `Spec ℚ`. -/
def mk {F : Sheaf (Scheme.fppfTopology.over base) (Type 1)}
    (p : SheafFieldValuedPoint F) : SheafPoints F :=
  Quotient.mk (SheafFieldValuedPoint.equivalentSetoid F) p

/-- Two field-valued points determine the same sheaf point exactly when they
admit a common field-valued extension. -/
theorem mk_eq_mk_iff {F : Sheaf (Scheme.fppfTopology.over base) (Type 1)}
    (p q : SheafFieldValuedPoint F) :
    mk p = mk q ↔ SheafFieldValuedPoint.Equivalent p q :=
  sorry

/-- The map on points induced by a morphism of fppf sheaves over `Spec ℚ`. -/
def map {F G : Sheaf (Scheme.fppfTopology.over base) (Type 1)} (f : F ⟶ G) :
    SheafPoints F → SheafPoints G :=
  Quotient.map (fun p ↦ p.map f) fun _ _ h ↦
    SheafFieldValuedPoint.Equivalent.map h f

/-- The induced map on sheaf points sends the class of a representative to the
class of its postcomposition. -/
theorem map_mk {F G : Sheaf (Scheme.fppfTopology.over base) (Type 1)}
    (f : F ⟶ G) (p : SheafFieldValuedPoint F) :
    map f (mk p) = mk (p.map f) :=
  sorry

end SheafPoints

/-- The sheaf fibre `Spec(K) ×_{Spec algebraicQ} X_{algebraicQ}` of
`toSpec_baseChange` along a morphism `Spec(K) ⟶ Spec algebraicQ` over
`Spec ℚ`. -/
abbrev toSpec_baseChange_fibre {K : Type} [Field K] [Algebra ℚ K]
    (σ : Over.mk (FieldExtension.specMap ℚ K) ⟶ cover) :
    Sheaf (Scheme.fppfTopology.over base) (Type 1) :=
  pullback toSpec_baseChange
    ((Scheme.fppfTopology.over base).uliftYoneda.{1}.map σ)

/-- `toSpec_baseChange_fibre σ` is the pullback of `toSpec_baseChange` along
the Yoneda image of `σ`. -/
theorem toSpec_baseChange_fibre_eq {K : Type} [Field K] [Algebra ℚ K]
    (σ : Over.mk (FieldExtension.specMap ℚ K) ⟶ cover) :
    toSpec_baseChange_fibre σ =
      pullback toSpec_baseChange
        ((Scheme.fppfTopology.over base).uliftYoneda.{1}.map σ) :=
  sorry

/-- A morphism of fppf sheaves over `Spec ℚ` exhibits the source as a reduced
induced structure on the target when the source is reduced, the morphism is a
closed immersion, and it is bijective on points. -/
structure IsReducedInduced {F G : Sheaf (Scheme.fppfTopology.over base) (Type 1)}
    (ι : F ⟶ G) : Prop where
  /-- The source admits a representable étale locally-surjective atlas from a
  reduced scheme. -/
  exists_reduced_etaleCover :
    ∃ (U : Over base)
      (p : (Scheme.fppfTopology.over base).uliftYoneda.{1}.obj U ⟶ F),
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).relative
          uliftYoneda.{1} p.hom ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over base) p.hom ∧
          AlgebraicGeometry.IsReduced U.left
  /-- The morphism is a closed immersion of fppf sheaves. -/
  isClosedImmersion :
    (MorphismProperty.over (@AlgebraicGeometry.IsClosedImmersion)).relative
      uliftYoneda.{1} ι.hom
  /-- The morphism is bijective on points. -/
  bijectiveOnPoints : Function.Bijective (SheafPoints.map ι)

/-- Construct `IsReducedInduced` from a reduced étale atlas, a closed immersion,
and bijectivity on points. -/
def IsReducedInduced.of {F G : Sheaf (Scheme.fppfTopology.over base) (Type 1)}
    (ι : F ⟶ G)
    (exists_reduced_etaleCover :
      ∃ (U : Over base)
        (p : (Scheme.fppfTopology.over base).uliftYoneda.{1}.obj U ⟶ F),
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).relative
            uliftYoneda.{1} p.hom ∧
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over base) p.hom ∧
            AlgebraicGeometry.IsReduced U.left)
    (isClosedImmersion :
      (MorphismProperty.over (@AlgebraicGeometry.IsClosedImmersion)).relative
        uliftYoneda.{1} ι.hom)
    (bijectiveOnPoints : Function.Bijective (SheafPoints.map ι)) :
    IsReducedInduced ι where
  exists_reduced_etaleCover := exists_reduced_etaleCover
  isClosedImmersion := isClosedImmersion
  bijectiveOnPoints := bijectiveOnPoints

/-- Unfolding of `IsReducedInduced`. -/
theorem IsReducedInduced.iff {F G : Sheaf (Scheme.fppfTopology.over base) (Type 1)}
    (ι : F ⟶ G) :
    IsReducedInduced ι ↔
      (∃ (U : Over base)
          (p : (Scheme.fppfTopology.over base).uliftYoneda.{1}.obj U ⟶ F),
          (MorphismProperty.over (@AlgebraicGeometry.Etale)).relative
              uliftYoneda.{1} p.hom ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over base) p.hom ∧
              AlgebraicGeometry.IsReduced U.left) ∧
        (MorphismProperty.over (@AlgebraicGeometry.IsClosedImmersion)).relative
            uliftYoneda.{1} ι.hom ∧
          Function.Bijective (SheafPoints.map ι) :=
  sorry

/-- Remark 76.3.5 (3): the base change of `toSpec` along
`Spec algebraicQ ⟶ Spec ℚ` is weakly radicial. -/
@[stacks 049E]
theorem toSpec_baseChange_weaklyRadicial :
    ∀ (K : Type) [Field K] [Algebra ℚ K]
      (σ : Over.mk (FieldExtension.specMap ℚ K) ⟶ cover),
      Nonempty (SheafPoints (toSpec_baseChange_fibre σ)) ∧
        Subsingleton (SheafPoints (toSpec_baseChange_fibre σ)) ∧
        ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ L) (_ : Algebra K L)
          (_ : IsPurelyInseparable K L)
          (ι : (Scheme.fppfTopology.over base).uliftYoneda.{1}.obj
                (Over.mk (FieldExtension.specMap ℚ L)) ⟶
              toSpec_baseChange_fibre σ),
            Mono ι ∧
              ι ≫ pullback.snd toSpec_baseChange
                    ((Scheme.fppfTopology.over base).uliftYoneda.{1}.map σ) =
                (Scheme.fppfTopology.over base).uliftYoneda.{1}.map
                  (specOver K L) :=
  sorry

/-- Remark 76.3.5 (4): the base change of `toSpec` along
`Spec algebraicQ ⟶ Spec ℚ` is not radicial. -/
@[stacks 049E]
theorem toSpec_baseChange_not_radicial :
    ∃ (F : Sheaf (Scheme.fppfTopology.over base) (Type 1))
      (ι : F ⟶ toSpec_baseChange_fibre (𝟙 cover)),
      IsReducedInduced ι ∧
        Nonempty (SheafPoints F) ∧
        ∀ (L : Type) [Field L] [Algebra ℚ L] [Algebra algebraicQ L]
          [IsPurelyInseparable algebraicQ L]
          (e : F ≅ (Scheme.fppfTopology.over base).uliftYoneda.{1}.obj
            (Over.mk (FieldExtension.specMap ℚ L))),
          e.hom ≫ (Scheme.fppfTopology.over base).uliftYoneda.{1}.map
              (specOver algebraicQ L) ≠
            ι ≫ pullback.snd toSpec_baseChange
              ((Scheme.fppfTopology.over base).uliftYoneda.{1}.map (𝟙 cover)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient
