/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback
public import Mathlib.RingTheory.TensorProduct.Maps
public import ReasLib.AlgebraicGeometry.WeilCohomology.ChernTheory

@[expose] public section

noncomputable section

universe u v w x y z q w' x' y' z' q'

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace WeilCohomology.ChernTheory

/-- An explicit scalar-extension comparison between raw D0/D1/D2' theories on
smooth-projective contexts. Its geometric functor is identified with canonical
field extension; its Chow comparison preserves pullback, pushforward, Cartier
classes, and diagonals, while its cohomology comparison preserves grading,
Tate shifts, naturality, cycle classes, and first Chern classes. -/
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
  /-- The graded comparison commutes with the Tate-shift equivalences. -/
  tateShift_compatible : ∀ X i j (a : T.Hgrade X (i, j))
      (t : TateLine) (s r : F'),
    cohomologyGradeEquiv X (i, j + 1)
        ((s * r) ⊗ₜ[F] T.tateTwist X i j (a ⊗ₜ[F] t)) =
      T'.tateTwist (baseChange.obj X) i j
        (cohomologyGradeEquiv X (i, j) (s ⊗ₜ[F] a) ⊗ₜ[F']
          tateEquiv (r ⊗ₜ[F] t))
  /-- The first-Chern square uses the canonical Picard pullback along
  `X_k' ⟶ X`. -/
  firstChernClass_commutes : ∀ X
      (L : (geometry.scheme.obj X).left.PicardGroup),
    cohomologyGradeEquiv X (2, 1) ((1 : F') ⊗ₜ[F] T.firstChernClass X L) =
      T'.firstChernClass (baseChange.obj X)
        (Scheme.Hom.picardPullback
          ((baseChangeIso.app X).inv.left ≫ FieldExtension.Over.toSource k k'
            (geometry.scheme.obj X)) L)
  /-- The cohomology comparison carries the canonical cycle-class map to the
  cycle-class map after Chow base change, once the first four axioms make both
  cycle-class systems canonical. -/
  cycleClass_commutes : T.InitialAxioms → T'.InitialAxioms →
    ∀ (gamma : T.CycleClass) (gamma' : T'.CycleClass) X (z : CH X),
      cohomologyEquiv X ((1 : F') ⊗ₜ[F] gamma.map X z) =
        gamma'.map (baseChange.obj X) (chowBaseChange X z)

namespace ScalarExtension

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
    tateShift_compatible := sorry
    firstChernClass_commutes := sorry
    cycleClass_commutes := sorry }

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
    e.cohomologyGradeEquiv X (2, 1) ((1 : F') ⊗ₜ[F] T.firstChernClass X L) =
      T'.firstChernClass (baseChange.obj X)
        (Scheme.Hom.picardPullback
          ((e.baseChangeIso.app X).inv.left ≫ FieldExtension.Over.toSource k k'
            (geometry.scheme.obj X)) L) := sorry

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
    (gamma' : T'.CycleClass) (X : V) (z : CH X) :
    e.cohomologyEquiv X ((1 : F') ⊗ₜ[F] gamma.map X z) =
      gamma'.map (baseChange.obj X) (e.chowBaseChange X z) := sorry

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
