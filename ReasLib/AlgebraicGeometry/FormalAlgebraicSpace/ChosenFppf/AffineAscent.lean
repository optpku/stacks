module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.TypeConditions

/-!
# Ascent along relatively affine morphisms on a chosen big fppf site

Affine formal algebraic spaces and their countable, classical, adic, and
Noetherian type conditions ascend along relatively affine morphisms.
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

/-- Let `S` be a scheme. Let `Y` be an affine formal
algebraic space. Let `f : X ⟶ Y` be a map of sheaves on `(Sch/S)_fppf` which
is representable and affine. Then `X` is an affine formal algebraic space. -/
theorem IsAffineFormalAlgebraicSpace.of_relativelyAffine
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAffineFormalAlgebraicSpace Y] {f : X ⟶ Y} (hf : relativelyAffine f) :
    IsAffineFormalAlgebraicSpace X :=
  sorry

/-- Let `S` be a scheme. Let `Y` be an affine formal
algebraic space. Let `f : X ⟶ Y` be a map of sheaves on `(Sch/S)_fppf` which
is representable and affine. If `Y` is countably indexed, then `X` is
countably indexed. -/
theorem IsCountablyIndexedAffine.of_relativelyAffine
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsCountablyIndexedAffine Y] {f : X ⟶ Y} (hf : relativelyAffine f) :
    IsCountablyIndexedAffine X :=
  sorry

/-- Let `S` be a scheme. Let `Y` be an affine formal
algebraic space. Let `f : X ⟶ Y` be a map of sheaves on `(Sch/S)_fppf` which
is representable and affine. If `Y` is countably indexed and classical, then
`X` is countably indexed and classical. -/
theorem IsClassicalAffine.of_relativelyAffine
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsCountablyIndexedAffine Y] [IsClassicalAffine Y]
    {f : X ⟶ Y} (hf : relativelyAffine f) :
    IsCountablyIndexedAffine X ∧ IsClassicalAffine X :=
  sorry

/-- Let `S` be a scheme. Let `Y` be an affine formal
algebraic space. Let `f : X ⟶ Y` be a map of sheaves on `(Sch/S)_fppf` which
is representable and affine. If `Y` is weakly adic, then `X` is weakly adic. -/
theorem IsWeaklyAdicAffine.of_relativelyAffine
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsWeaklyAdicAffine Y] {f : X ⟶ Y} (hf : relativelyAffine f) :
    IsWeaklyAdicAffine X :=
  sorry

/-- Let `S` be a scheme. Let `Y` be an affine formal
algebraic space. Let `f : X ⟶ Y` be a map of sheaves on `(Sch/S)_fppf` which
is representable and affine. If `Y` is adic*, then `X` is adic*. -/
theorem IsAdicStar.of_relativelyAffine
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAdicStar Y] {f : X ⟶ Y} (hf : relativelyAffine f) :
    IsAdicStar X :=
  sorry

/-- Let `S` be a scheme. Let `Y` be an affine formal
algebraic space. Let `f : X ⟶ Y` be a map of sheaves on `(Sch/S)_fppf` which
is representable and affine. If `Y` is Noetherian and `f` is locally of finite
type, then `X` is Noetherian. -/
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
