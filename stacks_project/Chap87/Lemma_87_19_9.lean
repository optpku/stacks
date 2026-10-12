/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_9_1_Affine
public import stacks_project.Chap87.Lemma_87_10_3_Types

/-!
# Lemma 87.19.9

An affine, representable map of fppf sheaves into an affine formal algebraic
space remains an affine formal algebraic space, and countably indexed,
classical, weakly adic, adic*, and Noetherian types ascend along it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- A morphism of sheaves on `(Sch/S)_fppf` is relatively affine when it is
relatively representable with respect to sheafified representables and every
represented pullback is affine after applying `𝒮.bigToScheme S`. -/
abbrev relativelyAffine {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y) : Prop :=
  (MorphismProperty.inverseImage (@IsAffineHom) (𝒮.bigToScheme S)).relative
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor f

/-- Relative affinity unpacks as the scheme-relative affine morphism property
with respect to sheafified representables. -/
theorem relativelyAffine_iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y) :
    relativelyAffine f ↔
      (MorphismProperty.inverseImage (@IsAffineHom) (𝒮.bigToScheme S)).relative
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor f :=
  sorry

/-- Relative affinity unpacks as relative representability together with
affinity of represented pullbacks on source schemes. -/
theorem relativelyAffine_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} {f : X ⟶ Y}
    (hf : relativelyAffine f) :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable f ∧
      ∀ {U V : 𝒮.bigSite S}
        (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ Y)
        (fst : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ X) (snd : V ⟶ U),
        IsPullback fst ((𝒮.bigTopology S).sheafifiedRepresentableMap snd) f ξ →
          IsAffineHom ((𝒮.bigToScheme S).map snd) :=
  sorry

/-- Lemma 87.19.9 (1): Let `S` be a scheme. Let `Y` be an affine formal
algebraic space. Let `f : X ⟶ Y` be a map of sheaves on `(Sch/S)_fppf` which
is representable and affine. Then `X` is an affine formal algebraic space. -/
@[stacks 0AKP]
theorem IsAffineFormalAlgebraicSpace.of_relativelyAffine
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAffineFormalAlgebraicSpace Y] {f : X ⟶ Y} (hf : relativelyAffine f) :
    IsAffineFormalAlgebraicSpace X :=
  sorry

/-- Lemma 87.19.9 (2): Let `S` be a scheme. Let `Y` be an affine formal
algebraic space. Let `f : X ⟶ Y` be a map of sheaves on `(Sch/S)_fppf` which
is representable and affine. If `Y` is countably indexed, then `X` is
countably indexed. -/
@[stacks 0AKP]
theorem IsCountablyIndexedAffine.of_relativelyAffine
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsCountablyIndexedAffine Y] {f : X ⟶ Y} (hf : relativelyAffine f) :
    IsCountablyIndexedAffine X :=
  sorry

/-- Lemma 87.19.9 (3): Let `S` be a scheme. Let `Y` be an affine formal
algebraic space. Let `f : X ⟶ Y` be a map of sheaves on `(Sch/S)_fppf` which
is representable and affine. If `Y` is countably indexed and classical, then
`X` is countably indexed and classical. -/
@[stacks 0AKP]
theorem IsClassicalAffine.of_relativelyAffine
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsCountablyIndexedAffine Y] [IsClassicalAffine Y]
    {f : X ⟶ Y} (hf : relativelyAffine f) :
    IsClassicalAffine X :=
  sorry

/-- Lemma 87.19.9 (4): Let `S` be a scheme. Let `Y` be an affine formal
algebraic space. Let `f : X ⟶ Y` be a map of sheaves on `(Sch/S)_fppf` which
is representable and affine. If `Y` is weakly adic, then `X` is weakly adic. -/
@[stacks 0AKP]
theorem IsWeaklyAdicAffine.of_relativelyAffine
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsWeaklyAdicAffine Y] {f : X ⟶ Y} (hf : relativelyAffine f) :
    IsWeaklyAdicAffine X :=
  sorry

/-- Lemma 87.19.9 (5): Let `S` be a scheme. Let `Y` be an affine formal
algebraic space. Let `f : X ⟶ Y` be a map of sheaves on `(Sch/S)_fppf` which
is representable and affine. If `Y` is adic*, then `X` is adic*. -/
@[stacks 0AKP]
theorem IsAdicStar.of_relativelyAffine
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAdicStar Y] {f : X ⟶ Y} (hf : relativelyAffine f) :
    IsAdicStar X :=
  sorry

/-- Lemma 87.19.9 (6): Let `S` be a scheme. Let `Y` be an affine formal
algebraic space. Let `f : X ⟶ Y` be a map of sheaves on `(Sch/S)_fppf` which
is representable and affine. If `Y` is Noetherian and `f` is locally of finite
type, then `X` is Noetherian. -/
@[stacks 0AKP]
theorem IsNoetherianAffine.of_relativelyAffine
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsNoetherianAffine Y] {f : X ⟶ Y} (hf : relativelyAffine f)
    (hft : (MorphismProperty.inverseImage (@LocallyOfFiniteType)
        (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor f) :
    IsNoetherianAffine X :=
  sorry

end AlgebraicGeometry
