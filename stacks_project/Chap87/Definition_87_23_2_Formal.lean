/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.Limits
public import stacks_project.Chap87.Definition_87_9_1_Affine

/-!
# Formal algebraic spaces

A sheaf on a chosen big fppf site `(Sch/S)_fppf` is a formal algebraic space when
it admits an étale jointly surjective atlas by affine formal algebraic spaces,
with each chart representable by algebraic spaces, and it satisfies the
coequalizer size condition on that same site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- A morphism of sheaves on `(Sch/S)_fppf` is relatively étale when it is
relatively representable with respect to sheafified representables and every
represented pullback is étale after applying `𝒮.bigToScheme S`. -/
def relativelyEtale {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y) : Prop :=
  (MorphismProperty.inverseImage (@Etale) (𝒮.bigToScheme S)).relative
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor f

/-- Relative étaleness unpacks as relative representability together with
étaleness of represented pullbacks on source schemes. -/
theorem relativelyEtale_iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y) :
    relativelyEtale f ↔
      (MorphismProperty.inverseImage (@Etale) (𝒮.bigToScheme S)).relative
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor f := sorry

/-- A represented pullback of a relatively étale sheaf morphism is étale on
source schemes. -/
theorem relativelyEtale.property {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} {f : X ⟶ Y}
    (hf : relativelyEtale f) {U V : 𝒮.bigSite S}
    (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ Y)
    (fst : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ X) (snd : V ⟶ U)
    (h : IsPullback fst ((𝒮.bigTopology S).sheafifiedRepresentableMap snd) f ξ) :
    Etale ((𝒮.bigToScheme S).map snd) := sorry

namespace ChosenBigFppfSite

/-- A sheaf on `(Sch/S)_fppf` is an algebraic space when its diagonal is
relatively representable by sheafified representables and it admits a
relatively étale locally surjective atlas from a sheafified representable. -/
class IsAlgebraicSpace {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop where
  /-- The diagonal of `X` is relatively representable with respect to
  sheafified representables. -/
  representableDiagonal :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable (diag X)
  /-- There is a relatively étale locally surjective atlas from a sheafified
  representable. -/
  atlas : ∃ (U : 𝒮.bigSite S)
      (p : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X),
        relativelyEtale p ∧ Sheaf.IsLocallySurjective p

namespace IsAlgebraicSpace

/-- The sheafified representable of an object of `(Sch/S)_fppf` is an algebraic
space. -/
instance instSheafifiedRepresentable {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (U : 𝒮.bigSite S) :
    IsAlgebraicSpace ((𝒮.bigTopology S).sheafifiedRepresentable U) := sorry

/-- A sheaf is an algebraic space iff its diagonal is relatively representable
and it admits a relatively étale locally surjective atlas. -/
theorem iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsAlgebraicSpace X ↔
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable (diag X) ∧
        ∃ (U : 𝒮.bigSite S)
          (p : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X),
            relativelyEtale p ∧ Sheaf.IsLocallySurjective p := sorry

/-- An algebraic space unpacks as a relatively representable diagonal together
with a relatively étale locally surjective atlas. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsAlgebraicSpace X] :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable (diag X) ∧
      ∃ (U : 𝒮.bigSite S)
        (p : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X),
          relativelyEtale p ∧ Sheaf.IsLocallySurjective p := sorry

end IsAlgebraicSpace

end ChosenBigFppfSite

/-- A morphism of sheaves on `(Sch/S)_fppf` is representable by algebraic spaces
when every base change along a sheafified representable is an algebraic space. -/
def representableByAlgebraicSpaces {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y) : Prop :=
  ∀ ⦃U : 𝒮.bigSite S⦄ (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ Y),
    ChosenBigFppfSite.IsAlgebraicSpace (pullback ξ f)

/-- Representability by algebraic spaces unpacks as algebraic-space-ness of
every base change along a sheafified representable. -/
theorem representableByAlgebraicSpaces_iff {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y) :
    representableByAlgebraicSpaces f ↔
      ∀ ⦃U : 𝒮.bigSite S⦄ (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ Y),
        ChosenBigFppfSite.IsAlgebraicSpace (pullback ξ f) := sorry

/-- The fibre product of a representable-by-algebraic-spaces morphism along a
sheafified representable is an algebraic space. -/
theorem representableByAlgebraicSpaces.isAlgebraicSpace_pullback
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} {f : X ⟶ Y}
    (hf : representableByAlgebraicSpaces f) {U : 𝒮.bigSite S}
    (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ Y) :
    ChosenBigFppfSite.IsAlgebraicSpace (pullback ξ f) := sorry

/-- A morphism of sheaves is representable by algebraic spaces as soon as every
fibre product along a sheafified representable is an algebraic space. -/
theorem representableByAlgebraicSpaces.of_isAlgebraicSpace_pullback
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} {f : X ⟶ Y}
    (h : ∀ ⦃U : 𝒮.bigSite S⦄ (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ Y),
      ChosenBigFppfSite.IsAlgebraicSpace (pullback ξ f)) :
    representableByAlgebraicSpaces f := sorry

/-- A sheaf on `(Sch/S)_fppf` is a formal algebraic space when it admits an
étale jointly surjective atlas by affine formal algebraic spaces, each chart
representable by algebraic spaces, and it satisfies the coequalizer size
condition. -/
class IsFormalAlgebraicSpace {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsCoequalizerOfRepresentables X where
  /-- There is an étale jointly surjective atlas by affine formal algebraic
  spaces whose charts are representable by algebraic spaces. -/
  exists_atlas :
    ∃ (ι : Type (max u v))
      (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
        (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
          (∀ i, representableByAlgebraicSpaces (π i)) ∧
            (∀ i, relativelyEtale (π i)) ∧
              Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π)

namespace IsFormalAlgebraicSpace

/-- An affine formal algebraic space is a formal algebraic space. -/
instance ofAffine {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] : IsFormalAlgebraicSpace X := sorry

/-- A sheaf is a formal algebraic space iff it satisfies the coequalizer size
condition and admits an étale jointly surjective affine atlas. -/
theorem iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsFormalAlgebraicSpace X ↔
      IsCoequalizerOfRepresentables X ∧
        ∃ (ι : Type (max u v))
          (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
            (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
              (∀ i, representableByAlgebraicSpaces (π i)) ∧
                (∀ i, relativelyEtale (π i)) ∧
                  Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) := sorry

/-- A formal algebraic space unpacks as an étale jointly surjective affine
atlas together with the coequalizer size condition. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsFormalAlgebraicSpace X] :
    ∃ (ι : Type (max u v))
      (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
        (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
          (∀ i, representableByAlgebraicSpaces (π i)) ∧
            (∀ i, relativelyEtale (π i)) ∧
              Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) ∧
                IsCoequalizerOfRepresentables X := sorry

end IsFormalAlgebraicSpace

end AlgebraicGeometry
