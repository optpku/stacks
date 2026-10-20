module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import stacks_project.Chap87.Lemma_87_16_2_Separated

/-!
# Separated morphisms of sheaves on a chosen big fppf site

A sheaf morphism on `(Sch/S)_fppf` is separated in the Bootstrap sense when
it is representable by algebraic spaces and every scheme base change has
relatively closed-immersion diagonal.

Object-level separated algebraic spaces reuse the existing owner
`ChosenBigFppfSite.IsSeparated` from Lemma 87.16.2.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry.ChosenBigFppfSite

/-- A morphism of sheaves on `(Sch/S)_fppf` is separated when it is
representable by algebraic spaces and, for every scheme `T` over `S` and
every `ξ : T ⟶ Y`, the relative diagonal of `X ×_Y T ⟶ T` is a closed
immersion relative to sheafified representables. -/
class Separated {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y) : Prop where
  /-- `f` is representable by algebraic spaces. -/
  representable : representableByAlgebraicSpaces f
  /-- For every scheme test `ξ : T ⟶ Y`, the relative diagonal of
  `X ×_Y T ⟶ T` is a closed immersion relative to sheafified representables. -/
  of_pullback :
    ∀ ⦃T : 𝒮.bigSite S⦄
      (ξ : (𝒮.bigTopology S).sheafifiedRepresentable T ⟶ Y),
      (MorphismProperty.inverseImage (@IsClosedImmersion)
        (𝒮.bigToScheme S)).relative
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor
        (pullback.diagonal (pullback.fst ξ f))

namespace Separated

/-- The sheafified representable of a separated morphism of `(Sch/S)_fppf` is
separated. -/
instance instSheafifiedRepresentableMap {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {U V : 𝒮.bigSite S} (f : U ⟶ V)
    [AlgebraicGeometry.IsSeparated ((𝒮.bigToScheme S).map f)] :
    Separated ((𝒮.bigTopology S).sheafifiedRepresentableMap f) := sorry

/-- The identity morphism of a sheaf on `(Sch/S)_fppf` is separated. -/
instance id {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))} : Separated (𝟙 X) := sorry

/-- An isomorphism of sheaves on `(Sch/S)_fppf` is separated. -/
instance of_isIso {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y) [IsIso f] :
    Separated f := sorry

/-- A sheaf morphism is separated iff it is representable by algebraic spaces
and every scheme base change has relatively closed-immersion diagonal. -/
theorem iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y) :
    Separated f ↔
      representableByAlgebraicSpaces f ∧
        ∀ ⦃T : 𝒮.bigSite S⦄
          (ξ : (𝒮.bigTopology S).sheafifiedRepresentable T ⟶ Y),
          (MorphismProperty.inverseImage (@IsClosedImmersion)
            (𝒮.bigToScheme S)).relative
            (𝒮.bigTopology S).sheafifiedRepresentableFunctor
            (pullback.diagonal (pullback.fst ξ f)) := sorry

/-- A separated sheaf morphism unpacks as representability by algebraic spaces
together with relatively closed-immersion diagonals of scheme base changes. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y)
    [Separated f] :
    representableByAlgebraicSpaces f ∧
      ∀ ⦃T : 𝒮.bigSite S⦄
        (ξ : (𝒮.bigTopology S).sheafifiedRepresentable T ⟶ Y),
        (MorphismProperty.inverseImage (@IsClosedImmersion)
          (𝒮.bigToScheme S)).relative
          (𝒮.bigTopology S).sheafifiedRepresentableFunctor
          (pullback.diagonal (pullback.fst ξ f)) := sorry

/-- Representability by algebraic spaces together with relatively
closed-immersion diagonals of scheme base changes witnesses that a sheaf
morphism is separated. -/
theorem of {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} {f : X ⟶ Y}
    (hrep : representableByAlgebraicSpaces f)
    (hpull :
      ∀ ⦃T : 𝒮.bigSite S⦄
        (ξ : (𝒮.bigTopology S).sheafifiedRepresentable T ⟶ Y),
        (MorphismProperty.inverseImage (@IsClosedImmersion)
          (𝒮.bigToScheme S)).relative
          (𝒮.bigTopology S).sheafifiedRepresentableFunctor
          (pullback.diagonal (pullback.fst ξ f))) :
    Separated f := sorry

/-- Scheme base changes of a separated sheaf morphism have relatively
closed-immersion diagonal. -/
theorem pullback_fst {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} {f : X ⟶ Y}
    [Separated f] {T : 𝒮.bigSite S}
    (ξ : (𝒮.bigTopology S).sheafifiedRepresentable T ⟶ Y) :
    (MorphismProperty.inverseImage (@IsClosedImmersion)
      (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor
      (pullback.diagonal (pullback.fst ξ f)) := sorry

end Separated

end AlgebraicGeometry.ChosenBigFppfSite
