/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension

/-!
# Families of curves of algebraic spaces

A morphism of algebraic spaces is a family of curves when it is locally of
finite presentation, quasi-compact, quasi-separated, flat, and proper, and
every étale scheme square over it has relative dimension at most 1. Over a
scheme, such a family becomes H-projective on an étale covering of the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- A morphism of algebraic spaces is a family of curves if it is locally of
finite presentation, quasi-compact, quasi-separated, flat, and proper, and
every étale scheme square over it has relative dimension at most 1. -/
class IsFamily {S : Scheme.{u}} {X T : AlgebraicSpace S} (f : X ⟶ T) : Prop where
  /-- The morphism is locally of finite presentation. -/
  locallyOfFinitePresentation : LocallyOfFinitePresentation f
  /-- The morphism is quasi-compact. -/
  quasiCompact : QuasiCompact f
  /-- The morphism is quasi-separated. -/
  quasiSeparated : QuasiSeparated f
  /-- The morphism is flat. -/
  flat : Flat f
  /-- The morphism is proper. -/
  proper : Proper f
  /-- Every étale scheme square over the morphism has relative dimension at most 1. -/
  relativeDimensionLE {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
      (b : yoneda.obj V ⟶ T.functorOfPoints) (h : U ⟶ V)
      (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
      (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
      (w : a ≫ f = yoneda.map h ≫ b) :
    Scheme.Hom.RelativeDimensionLE h.left 1

/-- A morphism of algebraic spaces is a family of curves if and only if it is
locally of finite presentation, quasi-compact, quasi-separated, flat, and
proper, and every étale scheme square over it has relative dimension at most 1. -/
theorem isFamily_iff {S : Scheme.{u}} {X T : AlgebraicSpace S} (f : X ⟶ T) :
    IsFamily f ↔
      LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f ∧
        Flat f ∧ Proper f ∧
          ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
            (b : yoneda.obj V ⟶ T.functorOfPoints) (h : U ⟶ V),
            (over (@AlgebraicGeometry.Etale)).presheaf a →
              (over (@AlgebraicGeometry.Etale)).presheaf b →
                a ≫ f = yoneda.map h ≫ b →
                  Scheme.Hom.RelativeDimensionLE h.left 1 :=
  ⟨fun hf =>
    ⟨hf.locallyOfFinitePresentation, hf.quasiCompact, hf.quasiSeparated, hf.flat,
      hf.proper, hf.relativeDimensionLE⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩⟩

/-- A family of curves is locally of finite presentation. -/
instance instLocallyOfFinitePresentation {S : Scheme.{u}} {X T : AlgebraicSpace S}
    (f : X ⟶ T) [h : IsFamily f] : LocallyOfFinitePresentation f :=
  h.locallyOfFinitePresentation

/-- A family of curves is quasi-compact. -/
instance instQuasiCompact {S : Scheme.{u}} {X T : AlgebraicSpace S}
    (f : X ⟶ T) [h : IsFamily f] : QuasiCompact f :=
  h.quasiCompact

/-- A family of curves is quasi-separated. -/
instance instQuasiSeparated {S : Scheme.{u}} {X T : AlgebraicSpace S}
    (f : X ⟶ T) [h : IsFamily f] : QuasiSeparated f :=
  h.quasiSeparated

/-- A family of curves is flat. -/
instance instFlat {S : Scheme.{u}} {X T : AlgebraicSpace S}
    (f : X ⟶ T) [h : IsFamily f] : Flat f :=
  h.flat

/-- A family of curves is proper. -/
instance instProper {S : Scheme.{u}} {X T : AlgebraicSpace S}
    (f : X ⟶ T) [h : IsFamily f] : Proper f :=
  h.proper

namespace IsFamily

/-- A family of curves is locally of finite presentation, quasi-compact,
quasi-separated, flat, and proper, and every étale scheme square over it has
relative dimension at most 1. -/
theorem spec {S : Scheme.{u}} {X T : AlgebraicSpace S} (f : X ⟶ T)
    [IsFamily f] :
    LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f ∧
      Flat f ∧ Proper f ∧
        ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
          (b : yoneda.obj V ⟶ T.functorOfPoints) (h : U ⟶ V),
          (over (@AlgebraicGeometry.Etale)).presheaf a →
            (over (@AlgebraicGeometry.Etale)).presheaf b →
              a ≫ f = yoneda.map h ≫ b →
                Scheme.Hom.RelativeDimensionLE h.left 1 :=
  (isFamily_iff f).mp inferInstance

end IsFamily

/-- A family of curves over a scheme admits an étale covering of the base such
that each fibre product is represented by a scheme that is H-projective over
the corresponding cover member. -/
theorem exists_etaleCovering_hProjective {B : Scheme.{u}} {X : AlgebraicSpace B}
    {S : Over B} (f : X ⟶ ofOver S) [IsFamily f] :
    ∃ 𝒰 : S.left.Cover.{u} Scheme.etalePrecoverage,
      ∀ i, ∃ (Y : Scheme.{u}) (π : Y ⟶ 𝒰.X i)
        (e : pullback f (ofOverHomMk (𝒰.f i) rfl) ≅
          ofOver (Over.mk (π ≫ 𝒰.f i ≫ S.hom))),
        HProjective π ∧
          e.hom ≫ ofOverHomMk π rfl =
            pullback.snd f (ofOverHomMk (𝒰.f i) rfl) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
