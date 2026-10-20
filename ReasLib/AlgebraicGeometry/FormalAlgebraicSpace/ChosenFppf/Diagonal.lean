/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Basic

/-!
# Diagonals of formal algebraic spaces

The diagonal of a formal algebraic space on a chosen big fppf site is
representable, a monomorphism, locally quasi-finite, locally of finite type,
and separated. For an affine formal algebraic space, it is a closed immersion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry
namespace IsAffineFormalAlgebraicSpace

/-- The diagonal of an affine formal algebraic space is a relative closed
immersion with respect to the sheafified representable functor. -/
theorem isClosedImmersion_diag {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    (MorphismProperty.inverseImage (@IsClosedImmersion) (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor (diag X) :=
  sorry

/-- The diagonal of an affine formal algebraic space is representable with
respect to the sheafified representable functor. -/
theorem relativelyRepresentable_diag {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable (diag X) :=
  (isClosedImmersion_diag X).1

/-- The diagonal of an affine formal algebraic space is relatively representable,
and every represented pullback projection is a closed immersion of schemes. -/
theorem isClosedImmersion_diag_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable (diag X) ∧
      ∀ {U V : 𝒮.bigSite S}
        (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X ⨯ X)
        (fst : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ X) (snd : V ⟶ U),
        IsPullback fst ((𝒮.bigTopology S).sheafifiedRepresentableMap snd) (diag X) ξ →
          IsClosedImmersion ((𝒮.bigToScheme S).map snd) :=
  isClosedImmersion_diag X

end IsAffineFormalAlgebraicSpace

namespace IsFormalAlgebraicSpace

/-- The diagonal of a formal algebraic space is representable, a relative
monomorphism, relatively locally quasi-finite, relatively locally of finite
type, and relatively separated with respect to the sheafified representable
functor. -/
theorem diagonal_properties {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable (diag X) ∧
      (MorphismProperty.inverseImage (MorphismProperty.monomorphisms Scheme)
          (𝒮.bigToScheme S)).relative
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor (diag X) ∧
      (MorphismProperty.inverseImage (@LocallyQuasiFinite) (𝒮.bigToScheme S)).relative
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor (diag X) ∧
      (MorphismProperty.inverseImage (@LocallyOfFiniteType) (𝒮.bigToScheme S)).relative
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor (diag X) ∧
      (MorphismProperty.inverseImage (@IsSeparated) (𝒮.bigToScheme S)).relative
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor (diag X) :=
  sorry

/-- The diagonal of a formal algebraic space is representable with
respect to the sheafified representable functor. -/
theorem relativelyRepresentable_diag {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable (diag X) :=
  (diagonal_properties X).1

/-- The diagonal of a formal algebraic space is a relative monomorphism
of schemes with respect to the sheafified representable functor. -/
theorem mono_diag {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (MorphismProperty.inverseImage (MorphismProperty.monomorphisms Scheme)
        (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor (diag X) :=
  (diagonal_properties X).2.1

/-- The diagonal of a formal algebraic space is relatively locally
quasi-finite with respect to the sheafified representable functor. -/
theorem locallyQuasiFinite_diag {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (MorphismProperty.inverseImage (@LocallyQuasiFinite) (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor (diag X) :=
  (diagonal_properties X).2.2.1

/-- The diagonal of a formal algebraic space is relatively locally of
finite type with respect to the sheafified representable functor. -/
theorem locallyOfFiniteType_diag {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (MorphismProperty.inverseImage (@LocallyOfFiniteType) (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor (diag X) :=
  (diagonal_properties X).2.2.2.1

/-- The diagonal of a formal algebraic space is relatively separated
with respect to the sheafified representable functor. -/
theorem isSeparated_diag {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (MorphismProperty.inverseImage (@IsSeparated) (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor (diag X) :=
  (diagonal_properties X).2.2.2.2

/-- Relative monomorphism of the diagonal unpacks as relative representability
together with monomorphisms of represented pullbacks on source schemes. -/
theorem mono_diag_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable (diag X) ∧
      ∀ {U V : 𝒮.bigSite S}
        (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X ⨯ X)
        (fst : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ X) (snd : V ⟶ U),
        IsPullback fst ((𝒮.bigTopology S).sheafifiedRepresentableMap snd) (diag X) ξ →
          Mono ((𝒮.bigToScheme S).map snd) :=
  mono_diag X

/-- Relative local quasi-finiteness of the diagonal unpacks as relative
representability together with locally quasi-finite represented pullbacks on
source schemes. -/
theorem locallyQuasiFinite_diag_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable (diag X) ∧
      ∀ {U V : 𝒮.bigSite S}
        (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X ⨯ X)
        (fst : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ X) (snd : V ⟶ U),
        IsPullback fst ((𝒮.bigTopology S).sheafifiedRepresentableMap snd) (diag X) ξ →
          LocallyQuasiFinite ((𝒮.bigToScheme S).map snd) :=
  locallyQuasiFinite_diag X

/-- Relative local finite type of the diagonal unpacks as relative
representability together with locally of finite type represented pullbacks on
source schemes. -/
theorem locallyOfFiniteType_diag_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable (diag X) ∧
      ∀ {U V : 𝒮.bigSite S}
        (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X ⨯ X)
        (fst : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ X) (snd : V ⟶ U),
        IsPullback fst ((𝒮.bigTopology S).sheafifiedRepresentableMap snd) (diag X) ξ →
          LocallyOfFiniteType ((𝒮.bigToScheme S).map snd) :=
  locallyOfFiniteType_diag X

/-- Relative separatedness of the diagonal unpacks as relative representability
together with separated represented pullbacks on source schemes. -/
theorem isSeparated_diag_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable (diag X) ∧
      ∀ {U V : 𝒮.bigSite S}
        (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X ⨯ X)
        (fst : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ X) (snd : V ⟶ U),
        IsPullback fst ((𝒮.bigTopology S).sheafifiedRepresentableMap snd) (diag X) ξ →
          IsSeparated ((𝒮.bigToScheme S).map snd) :=
  isSeparated_diag X

/-- The relative diagonal of a morphism of formal algebraic spaces is
representable, a relative monomorphism, relatively locally quasi-finite,
relatively locally of finite type, and relatively separated with respect to
the sheafified representable functor. -/
theorem relativeDiagonal_properties {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y) :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable
      (pullback.diagonal f) ∧
      (MorphismProperty.inverseImage (MorphismProperty.monomorphisms Scheme)
          (𝒮.bigToScheme S)).relative
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor (pullback.diagonal f) ∧
      (MorphismProperty.inverseImage (@LocallyQuasiFinite) (𝒮.bigToScheme S)).relative
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor (pullback.diagonal f) ∧
      (MorphismProperty.inverseImage (@LocallyOfFiniteType) (𝒮.bigToScheme S)).relative
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor (pullback.diagonal f) ∧
      (MorphismProperty.inverseImage (@IsSeparated) (𝒮.bigToScheme S)).relative
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor (pullback.diagonal f) :=
  sorry

/-- The relative diagonal of a morphism of formal algebraic spaces is
representable with respect to the sheafified representable functor. -/
theorem relativelyRepresentable_diagonal {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y) :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable
      (pullback.diagonal f) :=
  (relativeDiagonal_properties f).1

/-- The relative diagonal of a morphism of formal algebraic spaces is
a relative monomorphism of schemes with respect to the sheafified representable functor. -/
theorem mono_diagonal {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y) :
    (MorphismProperty.inverseImage (MorphismProperty.monomorphisms Scheme)
        (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor (pullback.diagonal f) :=
  (relativeDiagonal_properties f).2.1

/-- The relative diagonal of a morphism of formal algebraic spaces is
relatively locally quasi-finite with respect to the sheafified representable functor. -/
theorem locallyQuasiFinite_diagonal {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y) :
    (MorphismProperty.inverseImage (@LocallyQuasiFinite) (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor (pullback.diagonal f) :=
  (relativeDiagonal_properties f).2.2.1

/-- The relative diagonal of a morphism of formal algebraic spaces is
relatively locally of finite type with respect to the sheafified representable functor. -/
theorem locallyOfFiniteType_diagonal {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y) :
    (MorphismProperty.inverseImage (@LocallyOfFiniteType) (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor (pullback.diagonal f) :=
  (relativeDiagonal_properties f).2.2.2.1

/-- The relative diagonal of a morphism of formal algebraic spaces is
relatively separated with respect to the sheafified representable functor. -/
theorem isSeparated_diagonal {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y) :
    (MorphismProperty.inverseImage (@IsSeparated) (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor (pullback.diagonal f) :=
  (relativeDiagonal_properties f).2.2.2.2

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
  mono_diagonal f

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
  locallyQuasiFinite_diagonal f

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
  locallyOfFiniteType_diagonal f

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
  isSeparated_diagonal f


end IsFormalAlgebraicSpace
end AlgebraicGeometry
