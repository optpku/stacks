/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian

/-!
# Zero-dimensional algebraic spaces

Absolutely quasi-separated, locally-of-finite-type-over-a-field, and Noetherian
algebraic spaces of étale Krull dimension zero are separated schemes with affine
quasi-compact opens.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ZeroDimensional

/-- Every quasi-compact open of an absolutely quasi-separated algebraic space
of étale Krull dimension zero is affine. -/
theorem isAffine_of_isOpenImmersion
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X]
    (hdim : etaleKrullDim X = (0 : WithBot ℕ∞))
    {U : AlgebraicSpace S} (j : U ⟶ X) [IsOpenImmersion j] [IsQuasiCompact U] :
    IsAffine U := sorry

/-- An absolutely quasi-separated algebraic space of étale Krull dimension zero
has a representable functor of points. -/
theorem isRepresentable
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X]
    (hdim : etaleKrullDim X = (0 : WithBot ℕ∞)) :
    X.functorOfPoints.IsRepresentable := sorry

/-- An absolutely quasi-separated algebraic space of étale Krull dimension zero
is separated over the terminal scheme. -/
theorem isSeparated
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X]
    (hdim : etaleKrullDim X = (0 : WithBot ℕ∞)) :
    IsSeparated (extendBaseTerminal X) := sorry

/-- A quasi-compact absolutely quasi-separated algebraic space of étale Krull
dimension zero is affine. -/
theorem isAffine
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact X] (hdim : etaleKrullDim X = (0 : WithBot ℕ∞)) :
    IsAffine X := sorry

/-- Every quasi-compact open of an algebraic space of étale Krull dimension zero
that is locally of finite type over a field is affine. -/
theorem isAffine_of_isOpenImmersion_of_locallyOfFiniteType
    {S : Scheme.{u}} {X : AlgebraicSpace S} {k : Type u} [Field k]
    (f : extendBaseTerminal X ⟶ ofOver (Over.mk (terminal.from (Spec (.of k)))))
    [LocallyOfFiniteType f] (hdim : etaleKrullDim X = (0 : WithBot ℕ∞))
    {U : AlgebraicSpace S} (j : U ⟶ X) [IsOpenImmersion j] [IsQuasiCompact U] :
    IsAffine U := sorry

/-- An algebraic space of étale Krull dimension zero that is locally of finite
type over a field has a representable functor of points. -/
theorem isRepresentable_of_locallyOfFiniteType
    {S : Scheme.{u}} {X : AlgebraicSpace S} {k : Type u} [Field k]
    (f : extendBaseTerminal X ⟶ ofOver (Over.mk (terminal.from (Spec (.of k)))))
    [LocallyOfFiniteType f] (hdim : etaleKrullDim X = (0 : WithBot ℕ∞)) :
    X.functorOfPoints.IsRepresentable := sorry

/-- An algebraic space of étale Krull dimension zero that is locally of finite
type over a field is separated over the terminal scheme. -/
theorem isSeparated_of_locallyOfFiniteType
    {S : Scheme.{u}} {X : AlgebraicSpace S} {k : Type u} [Field k]
    (f : extendBaseTerminal X ⟶ ofOver (Over.mk (terminal.from (Spec (.of k)))))
    [LocallyOfFiniteType f] (hdim : etaleKrullDim X = (0 : WithBot ℕ∞)) :
    IsSeparated (extendBaseTerminal X) := sorry

/-- A quasi-compact algebraic space of étale Krull dimension zero that is
locally of finite type over a field is affine. -/
theorem isAffine_of_locallyOfFiniteType
    {S : Scheme.{u}} {X : AlgebraicSpace S} {k : Type u} [Field k]
    (f : extendBaseTerminal X ⟶ ofOver (Over.mk (terminal.from (Spec (.of k)))))
    [LocallyOfFiniteType f] [IsQuasiCompact X]
    (hdim : etaleKrullDim X = (0 : WithBot ℕ∞)) : IsAffine X := sorry

/-- Every quasi-compact open of an absolutely Noetherian algebraic space of
étale Krull dimension zero is affine. -/
theorem isAffine_of_isOpenImmersion_of_isNoetherian
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian (extendBaseTerminal X)]
    (hdim : etaleKrullDim X = (0 : WithBot ℕ∞))
    {U : AlgebraicSpace S} (j : U ⟶ X) [IsOpenImmersion j] [IsQuasiCompact U] :
    IsAffine U := sorry

/-- An absolutely Noetherian algebraic space of étale Krull dimension zero has
a representable functor of points. -/
theorem isRepresentable_of_isNoetherian
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian (extendBaseTerminal X)]
    (hdim : etaleKrullDim X = (0 : WithBot ℕ∞)) :
    X.functorOfPoints.IsRepresentable := sorry

/-- An absolutely Noetherian algebraic space of étale Krull dimension zero is
separated over the terminal scheme. -/
theorem isSeparated_of_isNoetherian
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian (extendBaseTerminal X)]
    (hdim : etaleKrullDim X = (0 : WithBot ℕ∞)) :
    IsSeparated (extendBaseTerminal X) := sorry

/-- An absolutely Noetherian algebraic space of étale Krull dimension zero is
affine. -/
theorem isAffine_of_isNoetherian
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian (extendBaseTerminal X)]
    (hdim : etaleKrullDim X = (0 : WithBot ℕ∞)) : IsAffine X := sorry

end AlgebraicGeometry.AlgebraicSpace.ZeroDimensional
