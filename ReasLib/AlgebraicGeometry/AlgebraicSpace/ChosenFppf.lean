module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.ChosenPresentation
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable

/-!
# Representability by algebraic spaces on a chosen big fppf site

Algebraic spaces, representability by algebraic spaces, and étaleness of
morphisms are defined for sheaves on a fixed site `(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology

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
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable
          (diag X) ∧
        ∃ (U : 𝒮.bigSite S)
          (p : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X),
            relativelyEtale p ∧ Sheaf.IsLocallySurjective p := sorry

/-- An algebraic space unpacks as a relatively representable diagonal together
with a relatively étale locally surjective atlas. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsAlgebraicSpace X] :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable
        (diag X) ∧
      ∃ (U : 𝒮.bigSite S)
        (p : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X),
          relativelyEtale p ∧ Sheaf.IsLocallySurjective p := sorry

end IsAlgebraicSpace

/-- A morphism of sheaves on `(Sch/S)_fppf` is representable by algebraic spaces
when every base change along a sheafified representable is an algebraic space. -/
def representableByAlgebraicSpaces {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y) : Prop :=
  ∀ ⦃U : 𝒮.bigSite S⦄ (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ Y),
    IsAlgebraicSpace (pullback ξ f)

/-- Representability by algebraic spaces unpacks as algebraic-space-ness of
every base change along a sheafified representable. -/
theorem representableByAlgebraicSpaces_iff {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y) :
    representableByAlgebraicSpaces f ↔
      ∀ ⦃U : 𝒮.bigSite S⦄ (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ Y),
        IsAlgebraicSpace (pullback ξ f) := sorry

/-- The fibre product of a representable-by-algebraic-spaces morphism along a
sheafified representable is an algebraic space. -/
theorem representableByAlgebraicSpaces.isAlgebraicSpace_pullback
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} {f : X ⟶ Y}
    (hf : representableByAlgebraicSpaces f) {U : 𝒮.bigSite S}
    (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ Y) :
    IsAlgebraicSpace (pullback ξ f) := sorry

/-- A morphism of sheaves is representable by algebraic spaces as soon as every
fibre product along a sheafified representable is an algebraic space. -/
theorem representableByAlgebraicSpaces.of_isAlgebraicSpace_pullback
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} {f : X ⟶ Y}
    (h : ∀ ⦃U : 𝒮.bigSite S⦄
      (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ Y),
        IsAlgebraicSpace (pullback ξ f)) :
    representableByAlgebraicSpaces f := sorry

/-- A morphism of algebraic-space sheaves on `(Sch/S)_fppf` is étale when
postcomposition preserves relative étaleness of morphisms from sheafified
representables. -/
def IsEtale {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y) : Prop :=
  ∀ ⦃U : 𝒮.bigSite S⦄ (φ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X),
    relativelyEtale φ → relativelyEtale (φ ≫ f)

/-- Étaleness of a morphism of algebraic-space sheaves unpacks as preservation
of relative étaleness under postcomposition. -/
theorem IsEtale_iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y) :
    IsEtale f ↔
      ∀ ⦃U : 𝒮.bigSite S⦄ (φ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X),
        relativelyEtale φ → relativelyEtale (φ ≫ f) := sorry

/-- An étale morphism of algebraic-space sheaves preserves relative étaleness
of morphisms from sheafified representables. -/
theorem IsEtale.spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} {f : X ⟶ Y}
    (hf : IsEtale f) {U : 𝒮.bigSite S}
    (φ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X)
    (hφ : relativelyEtale φ) : relativelyEtale (φ ≫ f) := sorry

/-- A morphism of sheaves on `(Sch/S)_fppf` is representable by algebraic spaces
and étale when every base change along a sheafified representable is an
algebraic space whose structure map is étale. -/
def etale {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y) : Prop :=
  representableByAlgebraicSpaces f ∧
    ∀ ⦃U : 𝒮.bigSite S⦄ (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ Y),
      IsEtale (pullback.fst ξ f)

/-- Representability by algebraic spaces and étaleness unpack as
representability together with étaleness of every scheme-base-change
structure map. -/
theorem etale_iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y) :
    etale f ↔
      representableByAlgebraicSpaces f ∧
        ∀ ⦃U : 𝒮.bigSite S⦄
          (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ Y),
            IsEtale (pullback.fst ξ f) := sorry

namespace etale

/-- A morphism that is representable by algebraic spaces and étale is
representable by algebraic spaces. -/
theorem representable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} {f : X ⟶ Y}
    (hf : etale f) : representableByAlgebraicSpaces f := sorry

/-- The structure map of a scheme base change of a representable-by-algebraic-
spaces étale morphism is étale. -/
theorem isEtale_fst {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} {f : X ⟶ Y}
    (hf : etale f) {U : 𝒮.bigSite S}
    (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ Y) :
    IsEtale (pullback.fst ξ f) := sorry

end etale

end ChosenBigFppfSite

end AlgebraicGeometry
