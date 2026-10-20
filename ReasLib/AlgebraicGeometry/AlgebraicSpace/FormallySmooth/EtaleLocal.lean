module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormallySmooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallySmooth

/-!
# Formal smoothness via étale scheme squares

A morphism of algebraic spaces is formally smooth if and only if every
commutative square with scheme vertices and étale vertical arrows has
formally smooth top arrow, and if and only if some such square with
surjective vertical arrows does.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FormallySmooth

/-- Every commutative square of schemes over `f` with étale vertical arrows has
formally smooth top arrow in the sense of `AlgebraicGeometry.FormallySmooth`. -/
def forallEtaleSchemeSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∀ {U V : Over S} (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (ψ : U ⟶ V),
    AlgebraicSpace.Etale a → AlgebraicSpace.Etale b →
      CommSq (ofOverMap ψ) a b f → AlgebraicGeometry.FormallySmooth ψ.left

/-- Every étale scheme square has formally smooth top arrow precisely when
the formally smooth scheme-chart condition holds for all its explicit square data. -/
theorem forallEtaleSchemeSquare_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    forallEtaleSchemeSquare f ↔
      ∀ {U V : Over S} (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (ψ : U ⟶ V),
        AlgebraicSpace.Etale a → AlgebraicSpace.Etale b →
          CommSq (ofOverMap ψ) a b f →
            AlgebraicGeometry.FormallySmooth ψ.left :=
  Iff.rfl

/-- There is a commutative square of schemes over `f` with étale surjective
vertical arrows and formally smooth top arrow. -/
def existsSurjectiveEtaleSchemeSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (ψ : U ⟶ V),
    AlgebraicSpace.Etale a ∧ AlgebraicSpace.Etale b ∧
      AlgebraicSpace.Surjective a ∧ AlgebraicSpace.Surjective b ∧
        CommSq (ofOverMap ψ) a b f ∧ AlgebraicGeometry.FormallySmooth ψ.left

/-- A formally smooth surjective étale scheme square exists precisely when
its scheme objects, arrows, and square hypotheses can be supplied. -/
theorem existsSurjectiveEtaleSchemeSquare_iff {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    existsSurjectiveEtaleSchemeSquare f ↔
      ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (ψ : U ⟶ V),
        AlgebraicSpace.Etale a ∧ AlgebraicSpace.Etale b ∧
          AlgebraicSpace.Surjective a ∧ AlgebraicSpace.Surjective b ∧
            CommSq (ofOverMap ψ) a b f ∧
              AlgebraicGeometry.FormallySmooth ψ.left :=
  Iff.rfl

/-- A morphism of algebraic spaces over `S` is formally
smooth if and only if every commutative square with scheme vertices and étale
vertical arrows has formally smooth top arrow. -/
theorem iff_forallEtaleSchemeSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : FormallySmooth f ↔ forallEtaleSchemeSquare f :=
  sorry

/-- A morphism of algebraic spaces over `S` is formally
smooth if and only if some commutative square with scheme vertices and étale
surjective vertical arrows has formally smooth top arrow. -/
theorem iff_existsSurjectiveEtaleSchemeSquare {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    FormallySmooth f ↔ existsSurjectiveEtaleSchemeSquare f :=
  sorry

/-- In a commutative square of schemes over a formally smooth morphism of
algebraic spaces, étale vertical arrows make the top arrow formally smooth. -/
theorem etaleSchemeSquare {S : Scheme.{u}} {U V : Over S}
    {X Y : AlgebraicSpace S} {ψ : U ⟶ V} {a : ofOver U ⟶ X} {b : ofOver V ⟶ Y}
    {f : X ⟶ Y} [AlgebraicSpace.Etale a] [AlgebraicSpace.Etale b]
    [FormallySmooth f] (sq : CommSq (ofOverMap ψ) a b f) :
    AlgebraicGeometry.FormallySmooth ψ.left :=
  (iff_forallEtaleSchemeSquare f).mp inferInstance a b ψ
    inferInstance inferInstance sq

/-- A commutative square of schemes with étale surjective vertical arrows and
formally smooth top arrow witnesses that the bottom morphism of algebraic spaces
is formally smooth. -/
theorem of_surjectiveEtaleSchemeSquare {S : Scheme.{u}} {U V : Over S}
    {X Y : AlgebraicSpace S} {ψ : U ⟶ V} {a : ofOver U ⟶ X} {b : ofOver V ⟶ Y}
    {f : X ⟶ Y} [AlgebraicSpace.Etale a] [AlgebraicSpace.Etale b]
    [AlgebraicSpace.Surjective a] [AlgebraicSpace.Surjective b]
    [AlgebraicGeometry.FormallySmooth ψ.left]
    (sq : CommSq (ofOverMap ψ) a b f) : FormallySmooth f :=
  (iff_existsSurjectiveEtaleSchemeSquare f).mpr
    ⟨U, V, a, b, ψ, inferInstance, inferInstance, inferInstance, inferInstance,
      sq, inferInstance⟩

/-- On a commutative square with étale surjective vertical arrows from schemes,
space-level formal smoothness of the bottom arrow is equivalent to
scheme-level formal smoothness of the top arrow. -/
theorem iff_of_surjectiveEtaleSchemeSquare {S : Scheme.{u}} {U V : Over S}
    {X Y : AlgebraicSpace S} {ψ : U ⟶ V} {a : ofOver U ⟶ X} {b : ofOver V ⟶ Y}
    {f : X ⟶ Y} [AlgebraicSpace.Etale a] [AlgebraicSpace.Etale b]
    [AlgebraicSpace.Surjective a] [AlgebraicSpace.Surjective b]
    (sq : CommSq (ofOverMap ψ) a b f) :
    FormallySmooth f ↔ AlgebraicGeometry.FormallySmooth ψ.left :=
  ⟨fun hf => (iff_forallEtaleSchemeSquare f).mp hf a b ψ
      inferInstance inferInstance sq,
    fun hψ => (iff_existsSurjectiveEtaleSchemeSquare f).mpr
      ⟨U, V, a, b, ψ, inferInstance, inferInstance, inferInstance, inferInstance,
        sq, hψ⟩⟩

end AlgebraicGeometry.AlgebraicSpace.FormallySmooth
