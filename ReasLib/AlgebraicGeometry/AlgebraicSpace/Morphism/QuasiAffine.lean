module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Basic

/-!
# Quasi-affine morphisms of algebraic spaces

A morphism of algebraic spaces is quasi-affine when every fibre product against an
affine scheme over the target is representable by a quasi-affine scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space over `S` is quasi-affine if it is representable by a
quasi-affine scheme over `S`. -/
@[mk_iff]
class IsQuasiAffine {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- There is a quasi-affine scheme over `S` whose associated algebraic space is
  isomorphic to `X`. -/
  exists_iso :
    ∃ (T : Over S), Nonempty (X ≅ ofOver T) ∧ T.left.IsQuasiAffine

namespace IsQuasiAffine

/-- A quasi-affine algebraic space is isomorphic to the algebraic space associated
to a quasi-affine scheme. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S) [IsQuasiAffine X] :
    ∃ (T : Over S), Nonempty (X ≅ ofOver T) ∧ T.left.IsQuasiAffine :=
  sorry

/-- An isomorphism with the algebraic space associated to a quasi-affine scheme
witnesses that an algebraic space is quasi-affine. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}
    (e : X ≅ ofOver T) [T.left.IsQuasiAffine] : IsQuasiAffine X :=
  sorry

/-- Quasi-affineness of algebraic spaces is invariant under isomorphism. -/
theorem of_iso {S : Scheme.{u}} {X Y : AlgebraicSpace S} (e : X ≅ Y)
    [IsQuasiAffine X] : IsQuasiAffine Y :=
  sorry

end IsQuasiAffine

/-- The algebraic space associated to a quasi-affine scheme is quasi-affine. -/
instance instIsQuasiAffine_ofOver {S : Scheme.{u}} (T : Over S)
    [hT : T.left.IsQuasiAffine] : IsQuasiAffine (ofOver T) where
  exists_iso := ⟨T, ⟨Iso.refl (ofOver T)⟩, hT⟩

/-- The algebraic space associated to a scheme `T` over `S` is quasi-affine if and
only if `T` is a quasi-affine scheme. -/
theorem isQuasiAffine_ofOver_iff {S : Scheme.{u}} (T : Over S) :
    IsQuasiAffine (ofOver T) ↔ T.left.IsQuasiAffine :=
  sorry

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` is quasi-affine if for every
affine scheme `Z` and morphism `Z ⟶ Y`, the fibre product `X ×_Y Z` is
representable by a quasi-affine scheme. -/
@[mk_iff]
class QuasiAffine {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- The vertex of an `IsPullback` square for `f` against an affine scheme is
  a quasi-affine algebraic space. -/
  pullback_isQuasiAffine {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S}
      {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X} :
      IsPullback pZ pX g f → IsQuasiAffine P

/-- A relatively representable morphism of algebraic spaces is quasi-affine exactly when
its represented pullback along every affine scheme is a quasi-affine scheme. -/
theorem quasiAffineHom_presheaf_iff_isQuasiAffine {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f) :
    (over (@QuasiAffineHom : MorphismProperty Scheme.{u})).presheaf f ↔
      ∀ {Z : Over S} [IsAffine Z.left]
        (g : yoneda.obj Z ⟶ Y.functorOfPoints),
        (hf.pullback g).left.IsQuasiAffine := sorry

namespace QuasiAffine

/-- The identity morphism of an algebraic space is quasi-affine. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : QuasiAffine (𝟙 X) := sorry

/-- An isomorphism of algebraic spaces is quasi-affine. -/
instance of_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIso f] :
    QuasiAffine f := sorry

/-- A quasi-affine morphism pulls affine schemes back to quasi-affine algebraic
spaces along any `IsPullback` square. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {Z : Over S}
    {P : AlgebraicSpace S} {f : X ⟶ Y} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X} [QuasiAffine f] [IsAffine Z.left]
    (h : IsPullback pZ pX g f) : IsQuasiAffine P :=
  sorry

/-- A universal affine-scheme pullback condition witnesses that a morphism of
algebraic spaces is quasi-affine. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S}
      {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
      IsPullback pZ pX g f → IsQuasiAffine P) : QuasiAffine f :=
  sorry

end QuasiAffine

/-- The chosen fibre product of a quasi-affine morphism with an affine scheme is a
quasi-affine algebraic space. -/
instance instIsQuasiAffine_pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {Z : Over S} (f : X ⟶ Y) (g : ofOver Z ⟶ Y) [QuasiAffine f]
    [IsAffine Z.left] [HasPullback f g] :
    IsQuasiAffine (pullback f g) :=
  sorry

namespace QuasiAffine

/-- Quasi-affine morphisms of algebraic spaces are stable under composition. -/
instance stableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@QuasiAffine S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composite of two quasi-affine morphisms of algebraic spaces is quasi-affine. -/
instance comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiAffine f] [QuasiAffine g] :
    QuasiAffine (f ≫ g) := sorry

end QuasiAffine

end AlgebraicGeometry.AlgebraicSpace
