module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_11_1_Formal

/-!
# Lemma 87.15.5

The relative diagonal of a morphism of formal algebraic spaces is representable,
a monomorphism, locally quasi-finite, locally of finite type, and separated, as a
representable transformation of fppf sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry.IsFormalAlgebraicSpace

/-- Lemma 87.15.5 (1): Let `S` be a scheme. If `f : X ⟶ Y` is a morphism of
formal algebraic spaces over `S`, then the diagonal morphism
`Δ : X ⟶ X ×_Y X` is representable. -/
@[stacks 0AN2]
theorem relativelyRepresentable_diagonal {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y) :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable
      (pullback.diagonal f) :=
  sorry

/-- Lemma 87.15.5 (2): Let `S` be a scheme. If `f : X ⟶ Y` is a morphism of
formal algebraic spaces over `S`, then the diagonal morphism
`Δ : X ⟶ X ×_Y X` is a monomorphism. -/
@[stacks 0AN2]
theorem mono_diagonal {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y) :
    (MorphismProperty.inverseImage (MorphismProperty.monomorphisms Scheme)
        (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor (pullback.diagonal f) :=
  sorry

/-- Lemma 87.15.5 (3): Let `S` be a scheme. If `f : X ⟶ Y` is a morphism of
formal algebraic spaces over `S`, then the diagonal morphism
`Δ : X ⟶ X ×_Y X` is locally quasi-finite. -/
@[stacks 0AN2]
theorem locallyQuasiFinite_diagonal {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y) :
    (MorphismProperty.inverseImage (@LocallyQuasiFinite) (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor (pullback.diagonal f) :=
  sorry

/-- Lemma 87.15.5 (4): Let `S` be a scheme. If `f : X ⟶ Y` is a morphism of
formal algebraic spaces over `S`, then the diagonal morphism
`Δ : X ⟶ X ×_Y X` is locally of finite type. -/
@[stacks 0AN2]
theorem locallyOfFiniteType_diagonal {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y) :
    (MorphismProperty.inverseImage (@LocallyOfFiniteType) (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor (pullback.diagonal f) :=
  sorry

/-- Lemma 87.15.5 (5): Let `S` be a scheme. If `f : X ⟶ Y` is a morphism of
formal algebraic spaces over `S`, then the diagonal morphism
`Δ : X ⟶ X ×_Y X` is separated. -/
@[stacks 0AN2]
theorem isSeparated_diagonal {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y) :
    (MorphismProperty.inverseImage (@IsSeparated) (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor (pullback.diagonal f) :=
  sorry

/-- Relative monomorphism of the relative diagonal unpacks as relative
representability together with monomorphisms of represented pullbacks on source
schemes. -/
theorem mono_diagonal_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y) :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable
        (pullback.diagonal f) ∧
      ∀ {U V : 𝒮.bigSite S}
        (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ pullback f f)
        (fst : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ X) (snd : V ⟶ U),
        IsPullback fst ((𝒮.bigTopology S).sheafifiedRepresentableMap snd)
          (pullback.diagonal f) ξ →
          Mono ((𝒮.bigToScheme S).map snd) :=
  sorry

/-- Relative local quasi-finiteness of the relative diagonal unpacks as relative
representability together with locally quasi-finite represented pullbacks on
source schemes. -/
theorem locallyQuasiFinite_diagonal_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y) :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable
        (pullback.diagonal f) ∧
      ∀ {U V : 𝒮.bigSite S}
        (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ pullback f f)
        (fst : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ X) (snd : V ⟶ U),
        IsPullback fst ((𝒮.bigTopology S).sheafifiedRepresentableMap snd)
          (pullback.diagonal f) ξ →
          LocallyQuasiFinite ((𝒮.bigToScheme S).map snd) :=
  sorry

/-- Relative local finite type of the relative diagonal unpacks as relative
representability together with locally of finite type represented pullbacks on
source schemes. -/
theorem locallyOfFiniteType_diagonal_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y) :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable
        (pullback.diagonal f) ∧
      ∀ {U V : 𝒮.bigSite S}
        (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ pullback f f)
        (fst : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ X) (snd : V ⟶ U),
        IsPullback fst ((𝒮.bigTopology S).sheafifiedRepresentableMap snd)
          (pullback.diagonal f) ξ →
          LocallyOfFiniteType ((𝒮.bigToScheme S).map snd) :=
  sorry

/-- Relative separatedness of the relative diagonal unpacks as relative
representability together with separated represented pullbacks on source
schemes. -/
theorem isSeparated_diagonal_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y) :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable
        (pullback.diagonal f) ∧
      ∀ {U V : 𝒮.bigSite S}
        (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ pullback f f)
        (fst : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ X) (snd : V ⟶ U),
        IsPullback fst ((𝒮.bigTopology S).sheafifiedRepresentableMap snd)
          (pullback.diagonal f) ξ →
          IsSeparated ((𝒮.bigToScheme S).map snd) :=
  sorry

end AlgebraicGeometry.IsFormalAlgebraicSpace
