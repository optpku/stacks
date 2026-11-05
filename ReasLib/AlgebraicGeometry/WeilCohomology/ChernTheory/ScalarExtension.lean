/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback
public import Mathlib.RingTheory.TensorProduct.Maps
public import ReasLib.AlgebraicGeometry.ChowGroup.FlatBaseChange
public import ReasLib.AlgebraicGeometry.WeilCohomology.ChernTheory

@[expose] public section

noncomputable section

universe u v w x y z q w' x' y' z' q'

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace WeilCohomology.SmoothProjectiveChow

/-- The actual flat field-extension pullback on total Chow homology, formed
degreewise from pullback of cycle representatives modulo rational equivalence. -/
def fieldExtensionPullback
    {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k']
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom] :
    ChowGroup.Total (fun _ ↦ 0) X →+
      ChowGroup.Total (fun _ ↦ 0) (FieldExtension.Over.baseChange k k' X) := by
  letI : IsLocallyNoetherian (FieldExtension.Over.baseChange k k' X).left :=
    LocallyOfFiniteType.isLocallyNoetherian (FieldExtension.Over.baseChange k k' X).hom
  exact DirectSum.toAddMonoid fun d ↦ (DirectSum.of _ d).comp
    ((ChowGroup.reindex
        ((FieldExtension.Over.baseChange k k' X).hom.relativeDimensionFunction
          (fun _ ↦ 0)) (add_zero d)).toAddMonoidHom.comp
      (ChowGroup.baseChangePullback (FieldExtension.specMap k k')
        (fun _ ↦ 0) (fun _ ↦ 0) 0 (by intro s s' hs'; rfl) X.hom d))

end WeilCohomology.SmoothProjectiveChow

namespace WeilCohomology.ChernTheory

/-- An explicit scalar-extension comparison between raw D0/D1/D2' theories on
smooth-projective contexts. Its geometric functor is identified with canonical
field extension; its Chow comparison preserves pullback, pushforward, Cartier
classes, and diagonals, while its cohomology comparison preserves grading,
Tate shifts, naturality, and first Chern classes. Cycle-class compatibility
is a consequence of the initial axioms, not part of the comparison data. -/
structure ScalarExtension
    {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
    {F : Type v} [Field F] [CharZero F]
    {F' : Type v} [Field F'] [CharZero F'] [Algebra F F']
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {TateLine' : Type x'} [AddCommGroup TateLine'] [Module F' TateLine']
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H : V → Type q} [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    {V' : Type w'} [Category.{z'} V']
    {dimension' : V' → ℕ} {product' : V' → V' → V'}
    {fst' : ∀ X Y, product' X Y ⟶ X} {snd' : ∀ X Y, product' X Y ⟶ Y}
    {point' : V'} {CH' : V' → Type y'} [∀ X, CommRing (CH' X)]
    {CHgrade' : ∀ X, ℤ → Submodule ℤ (CH' X)} [∀ X, GradedAlgebra (CHgrade' X)]
    {cyclePullback' : ∀ {X Y : V'}, (X ⟶ Y) → CHgrade' Y →ₐᵍ[ℤ] CHgrade' X}
    {cyclePushforward' : ∀ {X Y : V'}, (X ⟶ Y) → CH' X →+ CH' Y}
    {pointCycle' : CHgrade' point' 0}
    {geometry' : SmoothProjectiveContext k' V' dimension' product' fst' snd' point'
      CH' CHgrade' cyclePullback' cyclePushforward' pointCycle'}
    {H' : V' → Type q'} [∀ X, Ring (H' X)] [∀ X, Algebra F' (H' X)]
    (T : ChernTheory F TateLine geometry H)
    (T' : ChernTheory F' TateLine' geometry' H')
    (baseChange : V ⥤ V') where
  /-- The represented geometric functor is canonical extension of the base field. -/
  baseChangeIso : geometry.scheme ⋙ FieldExtension.Over.functor k k' ≅
    baseChange ⋙ geometry'.scheme
  /-- The degree-preserving base-change map on the canonical Chow rings. -/
  chowBaseChange : ∀ X, CHgrade X →ₐᵍ[ℤ] CHgrade' (baseChange.obj X)
  /-- The Chow comparison is the actual field-extension pullback: after cap
  with fundamental classes it is flat base change, transported along the given
  geometric presentation. This anchors the map independently of cohomology. -/
  chowBaseChange_eq : ∀ X (z : CH X),
    letI := geometry.smooth X
    letI := geometry.projective X
    letI := geometry'.smooth (baseChange.obj X)
    letI := geometry'.projective (baseChange.obj X)
    let eX : FieldExtension.Over.baseChange k k' (geometry.scheme.obj X) ≅
        geometry'.scheme.obj (baseChange.obj X) := baseChangeIso.app X
    SmoothProjectiveChow.capFundamental (geometry'.scheme.obj (baseChange.obj X))
        (geometry'.chowEquiv (baseChange.obj X) (chowBaseChange X z)) =
      ChowGroup.Total.map (fun _ ↦ 0) eX.hom
        (SmoothProjectiveChow.fieldExtensionPullback k' (geometry.scheme.obj X)
          (SmoothProjectiveChow.capFundamental (geometry.scheme.obj X)
            (geometry.chowEquiv X z)))
  /-- Chow base change commutes with pullback. -/
  chowBaseChange_pullback : ∀ {X Y : V} (f : X ⟶ Y) (z : CH Y),
    chowBaseChange X (cyclePullback f z) =
      cyclePullback' (baseChange.map f) (chowBaseChange Y z)
  /-- Base change of an effective Cartier divisor is again an effective Cartier divisor. -/
  cartierBaseChange : ∀ {Y X : V} (i : Y ⟶ X),
    IsEffectiveCartierDivisor (geometry.scheme.map i).left →
      IsEffectiveCartierDivisor (geometry'.scheme.map (baseChange.map i)).left
  /-- Canonical Cartier-divisor Picard classes commute with base change. -/
  cartierClass_compatible : ∀ {Y X : V} (i : Y ⟶ X)
      (hi : IsEffectiveCartierDivisor (geometry.scheme.map i).left),
    Scheme.Hom.picardPullback
        ((baseChangeIso.app X).inv.left ≫ FieldExtension.Over.toSource k k'
          (geometry.scheme.obj X))
        (effectiveCartierDivisorPicardClass (geometry.scheme.map i).left hi) =
      effectiveCartierDivisorPicardClass
        (geometry'.scheme.map (baseChange.map i)).left (cartierBaseChange i hi)
  /-- Base change preserves dimensions. -/
  dimension_compatible : ∀ X, dimension' (baseChange.obj X) = dimension X
  /-- Base change preserves the chosen product presentations. -/
  productIso : ∀ X Y,
    baseChange.obj (product X Y) ≅ product' (baseChange.obj X) (baseChange.obj Y)
  /-- A represented diagonal remains a represented diagonal after the product comparison. -/
  diagonal_compatible : ∀ {X : V} (diagonal : X ⟶ product X X),
    IsDiagonal geometry diagonal →
      IsDiagonal geometry'
        (baseChange.map diagonal ≫ (productIso X X).hom)
  /-- The base-changed Chow class of a represented diagonal is the Chow
  pushforward along the compared target diagonal. -/
  diagonalCycle_compatible : ∀ {X : V} (diagonal : X ⟶ product X X)
      (z : CHgrade (product X X) (dimension X)),
    IsDiagonalCycle cyclePushforward (dimension X) diagonal z →
      cyclePullback' (productIso X X).inv
          (chowBaseChange (product X X) z) =
        cyclePushforward'
          (baseChange.map diagonal ≫ (productIso X X).hom)
          (1 : CHgrade' (baseChange.obj X) 0)
  /-- Chow base change commutes with pushforward, in particular for divisor and
  diagonal cycles. -/
  chowBaseChange_pushforward : ∀ {X Y : V} (f : X ⟶ Y) (z : CH X),
    chowBaseChange Y (cyclePushforward f z) =
      cyclePushforward' (baseChange.map f) (chowBaseChange X z)
  /-- The comparison `F' ⊗[F] F(1) ≃ F'(1)`. -/
  tateEquiv : F' ⊗[F] TateLine ≃ₗ[F'] TateLine'
  /-- The functorial comparison on total cohomology as graded-algebra data. -/
  cohomologyEquiv : ∀ X, F' ⊗[F] H X ≃ₐ[F'] H' (baseChange.obj X)
  /-- The comparison restricted to each bidegree. -/
  cohomologyGradeEquiv : ∀ X p,
    F' ⊗[F] T.Hgrade X p ≃ₗ[F'] T'.Hgrade (baseChange.obj X) p
  /-- Pullback commutes with scalar extension. -/
  naturality : ∀ {X Y : V} (f : X ⟶ Y) (a : H Y) (s : F'),
    cohomologyEquiv X (s ⊗ₜ[F] T.pullback f a) =
      T'.pullback (baseChange.map f) (cohomologyEquiv Y (s ⊗ₜ[F] a))
  /-- The graded and total comparison maps agree on pure tensors. -/
  cohomologyGradeEquiv_coe : ∀ X p (a : T.Hgrade X p) (s : F'),
    (cohomologyGradeEquiv X p (s ⊗ₜ[F] a) : H' (baseChange.obj X)) =
      cohomologyEquiv X (s ⊗ₜ[F] (a : H X))
  /-- The first-Chern square uses the canonical Picard pullback along
  `X_k' ⟶ X`. -/
  firstChernClass_commutes : ∀ X
      (L : (geometry.scheme.obj X).left.PicardGroup),
    Tate.twistBaseChangeEquiv T.tateLine_rank tateEquiv (cohomologyGradeEquiv X 2) 1
        ((1 : F') ⊗ₜ[F] T.twistedFirstChernClass X L) =
      T'.twistedFirstChernClass (baseChange.obj X)
        (Scheme.Hom.picardPullback
          ((baseChangeIso.app X).inv.left ≫ FieldExtension.Over.toSource k k'
            (geometry.scheme.obj X)) L)

namespace ScalarExtension

/-- External comparison induced by the actual graded cohomology comparison
and the supplied Tate-line equivalence, including dual powers for negative twists. -/
def cohomologyTwistedEquiv
    {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
    {F : Type v} [Field F] [CharZero F]
    {F' : Type v} [Field F'] [CharZero F'] [Algebra F F']
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {TateLine' : Type x'} [AddCommGroup TateLine'] [Module F' TateLine']
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H : V → Type q} [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    {V' : Type w'} [Category.{z'} V']
    {dimension' : V' → ℕ} {product' : V' → V' → V'}
    {fst' : ∀ X Y, product' X Y ⟶ X} {snd' : ∀ X Y, product' X Y ⟶ Y}
    {point' : V'} {CH' : V' → Type y'} [∀ X, CommRing (CH' X)]
    {CHgrade' : ∀ X, ℤ → Submodule ℤ (CH' X)} [∀ X, GradedAlgebra (CHgrade' X)]
    {cyclePullback' : ∀ {X Y : V'}, (X ⟶ Y) → CHgrade' Y →ₐᵍ[ℤ] CHgrade' X}
    {cyclePushforward' : ∀ {X Y : V'}, (X ⟶ Y) → CH' X →+ CH' Y}
    {pointCycle' : CHgrade' point' 0}
    {geometry' : SmoothProjectiveContext k' V' dimension' product' fst' snd' point'
      CH' CHgrade' cyclePullback' cyclePushforward' pointCycle'}
    {H' : V' → Type q'} [∀ X, Ring (H' X)] [∀ X, Algebra F' (H' X)]
    {T : ChernTheory F TateLine geometry H}
    {T' : ChernTheory F' TateLine' geometry' H'} {baseChange : V ⥤ V'}
    (e : T.ScalarExtension T' baseChange) (X : V) (i n : ℤ) :
    F' ⊗[F] T.twistedGrade X i n ≃ₗ[F'] T'.twistedGrade (baseChange.obj X) i n :=
  Tate.twistBaseChangeEquiv T.tateLine_rank e.tateEquiv (e.cohomologyGradeEquiv X i) n

/-- The identity scalar-extension comparison, once the canonical identity-base-change
isomorphism of the geometric presentation is supplied. -/
noncomputable def refl
    {k : Type u} [Field k] {F : Type v} [Field F] [CharZero F]
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H : V → Type q} [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    (T : ChernTheory F TateLine geometry H)
    (baseChangeIso : geometry.scheme ⋙ FieldExtension.Over.functor k k ≅ geometry.scheme) :
    T.ScalarExtension T (𝟭 V) :=
  { baseChangeIso := baseChangeIso
    chowBaseChange := fun X ↦ GradedAlgHom.id ℤ (CHgrade X)
    chowBaseChange_eq := sorry
    chowBaseChange_pullback := sorry
    cartierBaseChange := sorry
    cartierClass_compatible := sorry
    dimension_compatible := sorry
    productIso := fun X Y ↦ Iso.refl (product X Y)
    diagonal_compatible := sorry
    diagonalCycle_compatible := sorry
    chowBaseChange_pushforward := sorry
    tateEquiv := TensorProduct.lid F TateLine
    cohomologyEquiv := fun X ↦ Algebra.TensorProduct.lid F (H X)
    cohomologyGradeEquiv := fun X p ↦ TensorProduct.lid F (T.Hgrade X p)
    naturality := sorry
    cohomologyGradeEquiv_coe := sorry
    firstChernClass_commutes := sorry }

/-- The naturality field evaluated on a pure tensor. -/
theorem naturality_apply
    {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
    {F : Type v} [Field F] [CharZero F]
    {F' : Type v} [Field F'] [CharZero F'] [Algebra F F']
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {TateLine' : Type x'} [AddCommGroup TateLine'] [Module F' TateLine']
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H : V → Type q} [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    {V' : Type w'} [Category.{z'} V']
    {dimension' : V' → ℕ} {product' : V' → V' → V'}
    {fst' : ∀ X Y, product' X Y ⟶ X} {snd' : ∀ X Y, product' X Y ⟶ Y}
    {point' : V'} {CH' : V' → Type y'} [∀ X, CommRing (CH' X)]
    {CHgrade' : ∀ X, ℤ → Submodule ℤ (CH' X)} [∀ X, GradedAlgebra (CHgrade' X)]
    {cyclePullback' : ∀ {X Y : V'}, (X ⟶ Y) → CHgrade' Y →ₐᵍ[ℤ] CHgrade' X}
    {cyclePushforward' : ∀ {X Y : V'}, (X ⟶ Y) → CH' X →+ CH' Y}
    {pointCycle' : CHgrade' point' 0}
    {geometry' : SmoothProjectiveContext k' V' dimension' product' fst' snd' point'
      CH' CHgrade' cyclePullback' cyclePushforward' pointCycle'}
    {H' : V' → Type q'} [∀ X, Ring (H' X)] [∀ X, Algebra F' (H' X)]
    {T : ChernTheory F TateLine geometry H}
    {T' : ChernTheory F' TateLine' geometry' H'} {baseChange : V ⥤ V'}
    (e : T.ScalarExtension T' baseChange) {X Y : V}
    (f : X ⟶ Y) (a : H Y) (s : F') :
    e.cohomologyEquiv X (s ⊗ₜ[F] T.pullback f a) =
      T'.pullback (baseChange.map f) (e.cohomologyEquiv Y (s ⊗ₜ[F] a)) := sorry

/-- The comparison carries a first Chern class to the first Chern class of its
canonical base change. -/
theorem firstChernClass_commutes_apply
    {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
    {F : Type v} [Field F] [CharZero F]
    {F' : Type v} [Field F'] [CharZero F'] [Algebra F F']
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {TateLine' : Type x'} [AddCommGroup TateLine'] [Module F' TateLine']
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H : V → Type q} [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    {V' : Type w'} [Category.{z'} V']
    {dimension' : V' → ℕ} {product' : V' → V' → V'}
    {fst' : ∀ X Y, product' X Y ⟶ X} {snd' : ∀ X Y, product' X Y ⟶ Y}
    {point' : V'} {CH' : V' → Type y'} [∀ X, CommRing (CH' X)]
    {CHgrade' : ∀ X, ℤ → Submodule ℤ (CH' X)} [∀ X, GradedAlgebra (CHgrade' X)]
    {cyclePullback' : ∀ {X Y : V'}, (X ⟶ Y) → CHgrade' Y →ₐᵍ[ℤ] CHgrade' X}
    {cyclePushforward' : ∀ {X Y : V'}, (X ⟶ Y) → CH' X →+ CH' Y}
    {pointCycle' : CHgrade' point' 0}
    {geometry' : SmoothProjectiveContext k' V' dimension' product' fst' snd' point'
      CH' CHgrade' cyclePullback' cyclePushforward' pointCycle'}
    {H' : V' → Type q'} [∀ X, Ring (H' X)] [∀ X, Algebra F' (H' X)]
    {T : ChernTheory F TateLine geometry H}
    {T' : ChernTheory F' TateLine' geometry' H'} {baseChange : V ⥤ V'}
    (e : T.ScalarExtension T' baseChange) (X : V)
    (L : (geometry.scheme.obj X).left.PicardGroup) :
    e.cohomologyTwistedEquiv X 2 1 ((1 : F') ⊗ₜ[F] T.twistedFirstChernClass X L) =
      T'.twistedFirstChernClass (baseChange.obj X)
        (Scheme.Hom.picardPullback
          ((e.baseChangeIso.app X).inv.left ≫ FieldExtension.Over.toSource k k'
            (geometry.scheme.obj X)) L) :=
  e.firstChernClass_commutes X L

/-- Cycle classes commute with scalar extension under (A1)--(A4) on both sides.

As in Stacks 0FVT, write a rational Chow class as a Chern character capped
with the fundamental class. The geometric anchoring `chowBaseChange_eq`
identifies its pullback with the Chern character of the pulled-back bundle.
The projective-bundle formula and splitting principle then reduce comparison
to `firstChernClass_commutes`. No cycle-class comparison is an input. -/
theorem cycleClass_commutes
    {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
    {F : Type v} [Field F] [CharZero F]
    {F' : Type v} [Field F'] [CharZero F'] [Algebra F F']
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {TateLine' : Type x'} [AddCommGroup TateLine'] [Module F' TateLine']
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H : V → Type q} [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    {V' : Type w'} [Category.{z'} V']
    {dimension' : V' → ℕ} {product' : V' → V' → V'}
    {fst' : ∀ X Y, product' X Y ⟶ X} {snd' : ∀ X Y, product' X Y ⟶ Y}
    {point' : V'} {CH' : V' → Type y'} [∀ X, CommRing (CH' X)]
    {CHgrade' : ∀ X, ℤ → Submodule ℤ (CH' X)} [∀ X, GradedAlgebra (CHgrade' X)]
    {cyclePullback' : ∀ {X Y : V'}, (X ⟶ Y) → CHgrade' Y →ₐᵍ[ℤ] CHgrade' X}
    {cyclePushforward' : ∀ {X Y : V'}, (X ⟶ Y) → CH' X →+ CH' Y}
    {pointCycle' : CHgrade' point' 0}
    {geometry' : SmoothProjectiveContext k' V' dimension' product' fst' snd' point'
      CH' CHgrade' cyclePullback' cyclePushforward' pointCycle'}
    {H' : V' → Type q'} [∀ X, Ring (H' X)] [∀ X, Algebra F' (H' X)]
    {T : ChernTheory F TateLine geometry H}
    {T' : ChernTheory F' TateLine' geometry' H'} {baseChange : V ⥤ V'}
    (e : T.ScalarExtension T' baseChange) (h : T.InitialAxioms)
    (h' : T'.InitialAxioms) (gamma : T.CycleClass)
    (gamma' : T'.CycleClass) (X : V) (i : ℤ) (z : CHgrade X i) :
    e.cohomologyTwistedEquiv X (2 * i) i ((1 : F') ⊗ₜ[F] gamma.twistedMap X i z) =
      gamma'.twistedMap (baseChange.obj X) i
        ⟨e.chowBaseChange X z, (e.chowBaseChange X).map_mem z.property⟩ := by
  sorry

/-- The cycle-class comparison evaluated on a Chow class. -/
theorem cycleClass_commutes_apply
    {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
    {F : Type v} [Field F] [CharZero F]
    {F' : Type v} [Field F'] [CharZero F'] [Algebra F F']
    {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
    {TateLine' : Type x'} [AddCommGroup TateLine'] [Module F' TateLine']
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H : V → Type q} [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    {V' : Type w'} [Category.{z'} V']
    {dimension' : V' → ℕ} {product' : V' → V' → V'}
    {fst' : ∀ X Y, product' X Y ⟶ X} {snd' : ∀ X Y, product' X Y ⟶ Y}
    {point' : V'} {CH' : V' → Type y'} [∀ X, CommRing (CH' X)]
    {CHgrade' : ∀ X, ℤ → Submodule ℤ (CH' X)} [∀ X, GradedAlgebra (CHgrade' X)]
    {cyclePullback' : ∀ {X Y : V'}, (X ⟶ Y) → CHgrade' Y →ₐᵍ[ℤ] CHgrade' X}
    {cyclePushforward' : ∀ {X Y : V'}, (X ⟶ Y) → CH' X →+ CH' Y}
    {pointCycle' : CHgrade' point' 0}
    {geometry' : SmoothProjectiveContext k' V' dimension' product' fst' snd' point'
      CH' CHgrade' cyclePullback' cyclePushforward' pointCycle'}
    {H' : V' → Type q'} [∀ X, Ring (H' X)] [∀ X, Algebra F' (H' X)]
    {T : ChernTheory F TateLine geometry H}
    {T' : ChernTheory F' TateLine' geometry' H'} {baseChange : V ⥤ V'}
    (e : T.ScalarExtension T' baseChange) (h : T.InitialAxioms)
    (h' : T'.InitialAxioms) (gamma : T.CycleClass)
    (gamma' : T'.CycleClass) (X : V) (i : ℤ) (z : CHgrade X i) :
    e.cohomologyTwistedEquiv X (2 * i) i ((1 : F') ⊗ₜ[F] gamma.twistedMap X i z) =
      gamma'.twistedMap (baseChange.obj X) i
        ⟨e.chowBaseChange X z, (e.chowBaseChange X).map_mem z.property⟩ :=
  e.cycleClass_commutes h h' gamma gamma' X i z

end ScalarExtension

/-- A scalar-extension comparison transfers the full axiom bundle from the
extended Chern theory to the original Chern theory. -/
theorem axiomsOfScalarExtension
    {k : Type u} [Field k] {k' : Type u} [Field k'] [Algebra k k']
    {F : Type v} [Field F] [CharZero F]
    {F' : Type v} [Field F'] [CharZero F'] [Algebra F F']
    {TateLine : Type x} {TateLine' : Type x'}
    [AddCommGroup TateLine] [Module F TateLine]
    [AddCommGroup TateLine'] [Module F' TateLine']
    {V : Type w} [Category.{z} V]
    {dimension : V → ℕ} {product : V → V → V}
    {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
    {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
    {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
    {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
    {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
    {pointCycle : CHgrade point 0}
    {geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle}
    {H : V → Type q} [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    {V' : Type w'} [Category.{z'} V']
    {dimension' : V' → ℕ} {product' : V' → V' → V'}
    {fst' : ∀ X Y, product' X Y ⟶ X} {snd' : ∀ X Y, product' X Y ⟶ Y}
    {point' : V'} {CH' : V' → Type y'} [∀ X, CommRing (CH' X)]
    {CHgrade' : ∀ X, ℤ → Submodule ℤ (CH' X)} [∀ X, GradedAlgebra (CHgrade' X)]
    {cyclePullback' : ∀ {X Y : V'}, (X ⟶ Y) → CHgrade' Y →ₐᵍ[ℤ] CHgrade' X}
    {cyclePushforward' : ∀ {X Y : V'}, (X ⟶ Y) → CH' X →+ CH' Y}
    {pointCycle' : CHgrade' point' 0}
    {geometry' : SmoothProjectiveContext k' V' dimension' product' fst' snd' point'
      CH' CHgrade' cyclePullback' cyclePushforward' pointCycle'}
    {H' : V' → Type q'} [∀ X, Ring (H' X)] [∀ X, Algebra F' (H' X)]
    (baseChange : V ⥤ V')
    (T : ChernTheory F TateLine geometry H)
    (T' : ChernTheory F' TateLine' geometry' H')
    (e : T.ScalarExtension T' baseChange)
    (h' : T'.Axioms) : T.Axioms := sorry

end WeilCohomology.ChernTheory
