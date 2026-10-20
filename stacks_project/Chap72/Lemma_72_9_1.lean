module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZeroDimensional

/-!
# Dimension zero algebraic spaces

An algebraic space of dimension zero that is absolutely quasi-separated, locally
of finite type over a field, or Noetherian is a separated scheme, and every
quasi-compact open subspace is affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 72.9.1 (1): An absolutely quasi-separated algebraic space of étale Krull
dimension zero is a separated scheme, and every quasi-compact open is affine. -/
@[stacks 06LZ] #check
  (AlgebraicGeometry.AlgebraicSpace.ZeroDimensional.isAffine_of_isOpenImmersion :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X],
      etaleKrullDim X = (0 : WithBot ℕ∞) →
      ∀ {U : AlgebraicSpace S} (j : U ⟶ X) [IsOpenImmersion j] [IsQuasiCompact U],
        IsAffine U)

#check (AlgebraicGeometry.AlgebraicSpace.ZeroDimensional.isRepresentable :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X],
    etaleKrullDim X = (0 : WithBot ℕ∞) → X.functorOfPoints.IsRepresentable)

#check (AlgebraicGeometry.AlgebraicSpace.ZeroDimensional.isSeparated :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X],
    etaleKrullDim X = (0 : WithBot ℕ∞) → IsSeparated (extendBaseTerminal X))

#check (AlgebraicGeometry.AlgebraicSpace.ZeroDimensional.isAffine :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact X], etaleKrullDim X = (0 : WithBot ℕ∞) → IsAffine X)

/- Lemma 72.9.1 (2): An algebraic space of étale Krull dimension zero that is
locally of finite type over a field is a separated scheme, and every
quasi-compact open is affine. -/
@[stacks 06LZ] #check
  (AlgebraicGeometry.AlgebraicSpace.ZeroDimensional.isAffine_of_isOpenImmersion_of_locallyOfFiniteType :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {k : Type u} [Field k]
      (f : extendBaseTerminal X ⟶ ofOver (Over.mk (terminal.from (Spec (.of k)))))
      [LocallyOfFiniteType f], etaleKrullDim X = (0 : WithBot ℕ∞) →
      ∀ {U : AlgebraicSpace S} (j : U ⟶ X) [IsOpenImmersion j] [IsQuasiCompact U],
        IsAffine U)

#check (AlgebraicGeometry.AlgebraicSpace.ZeroDimensional.isRepresentable_of_locallyOfFiniteType :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {k : Type u} [Field k]
    (f : extendBaseTerminal X ⟶ ofOver (Over.mk (terminal.from (Spec (.of k)))))
    [LocallyOfFiniteType f], etaleKrullDim X = (0 : WithBot ℕ∞) →
      X.functorOfPoints.IsRepresentable)

#check (AlgebraicGeometry.AlgebraicSpace.ZeroDimensional.isSeparated_of_locallyOfFiniteType :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {k : Type u} [Field k]
    (f : extendBaseTerminal X ⟶ ofOver (Over.mk (terminal.from (Spec (.of k)))))
    [LocallyOfFiniteType f], etaleKrullDim X = (0 : WithBot ℕ∞) →
      IsSeparated (extendBaseTerminal X))

#check (AlgebraicGeometry.AlgebraicSpace.ZeroDimensional.isAffine_of_locallyOfFiniteType :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {k : Type u} [Field k]
    (f : extendBaseTerminal X ⟶ ofOver (Over.mk (terminal.from (Spec (.of k)))))
    [LocallyOfFiniteType f] [IsQuasiCompact X],
    etaleKrullDim X = (0 : WithBot ℕ∞) → IsAffine X)

/- Lemma 72.9.1 (3): A Noetherian algebraic space of étale Krull dimension zero
is a separated scheme, and every quasi-compact open is affine. -/
@[stacks 06LZ] #check
  (AlgebraicGeometry.AlgebraicSpace.ZeroDimensional.isAffine_of_isOpenImmersion_of_isNoetherian :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian (extendBaseTerminal X)],
      etaleKrullDim X = (0 : WithBot ℕ∞) →
      ∀ {U : AlgebraicSpace S} (j : U ⟶ X) [IsOpenImmersion j] [IsQuasiCompact U],
        IsAffine U)

#check (AlgebraicGeometry.AlgebraicSpace.ZeroDimensional.isRepresentable_of_isNoetherian :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian (extendBaseTerminal X)],
    etaleKrullDim X = (0 : WithBot ℕ∞) → X.functorOfPoints.IsRepresentable)

#check (AlgebraicGeometry.AlgebraicSpace.ZeroDimensional.isSeparated_of_isNoetherian :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian (extendBaseTerminal X)],
    etaleKrullDim X = (0 : WithBot ℕ∞) → IsSeparated (extendBaseTerminal X))

#check (AlgebraicGeometry.AlgebraicSpace.ZeroDimensional.isAffine_of_isNoetherian :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian (extendBaseTerminal X)],
    etaleKrullDim X = (0 : WithBot ℕ∞) → IsAffine X)

end AlgebraicGeometry.AlgebraicSpace
