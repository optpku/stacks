/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Groupoid.InFunctors
public import ReasLib.AlgebraicGeometry.FormalDeformation.TypesCompletion.Morphism

/-!
# Completion of a groupoid in functors

The completion of a groupoid in functors on `ArtinianLocalAlgCat` is the groupoid in
functors on `CompleteLocalAlgCat` obtained by completing the object and arrow functors
and the structure maps, transporting composition along the canonical pullback
comparison for set-valued completion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

/-- The source of a completed composite is the source of its earlier arrow. -/
private theorem completion_comp_source
    (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)) :
    ((Functor.typesCompletionPullbackIso G.s G.t).inv ≫ Functor.typesCompletionMap G.c) ≫
        Functor.typesCompletionMap G.s =
      pullback.snd (Functor.typesCompletionMap G.s) (Functor.typesCompletionMap G.t) ≫
        Functor.typesCompletionMap G.s := sorry

/-- The target of a completed composite is the target of its later arrow. -/
private theorem completion_comp_target
    (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)) :
    ((Functor.typesCompletionPullbackIso G.s G.t).inv ≫ Functor.typesCompletionMap G.c) ≫
        Functor.typesCompletionMap G.t =
      pullback.fst (Functor.typesCompletionMap G.s) (Functor.typesCompletionMap G.t) ≫
        Functor.typesCompletionMap G.t := sorry

/-- Completed identity arrows have the specified source. -/
private theorem completion_identity_source
    (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)) :
    Functor.typesCompletionMap G.e ≫ Functor.typesCompletionMap G.s =
      𝟙 (Functor.typesCompletion G.U) := sorry

/-- Completed identity arrows have the specified target. -/
private theorem completion_identity_target
    (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)) :
    Functor.typesCompletionMap G.e ≫ Functor.typesCompletionMap G.t =
      𝟙 (Functor.typesCompletion G.U) := sorry

/-- Completed inversion exchanges source with target. -/
private theorem completion_inverse_source
    (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)) :
    Functor.typesCompletionMap G.i ≫ Functor.typesCompletionMap G.s =
      Functor.typesCompletionMap G.t := sorry

/-- Completed inversion exchanges target with source. -/
private theorem completion_inverse_target
    (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)) :
    Functor.typesCompletionMap G.i ≫ Functor.typesCompletionMap G.t =
      Functor.typesCompletionMap G.s := sorry

/-- The transported completed composition is associative on generalized arrows. -/
private theorem completion_associativity
    (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)) :
    let source := Functor.typesCompletionMap G.s
    let target := Functor.typesCompletionMap G.t
    let compose := (Functor.typesCompletionPullbackIso G.s G.t).inv ≫
      Functor.typesCompletionMap G.c
    ∀ {W : CompleteLocalAlgCat Λ k ⥤ Type w}
      (later middle earlier : W ⟶ Functor.typesCompletion G.R)
      (h_later_middle : later ≫ source = middle ≫ target)
      (h_middle_earlier : middle ≫ source = earlier ≫ target)
      (h_composite_earlier : (pullback.lift later middle h_later_middle ≫ compose) ≫
        source = earlier ≫ target)
      (h_later_composite : later ≫ source =
        (pullback.lift middle earlier h_middle_earlier ≫ compose) ≫ target),
      pullback.lift (pullback.lift later middle h_later_middle ≫ compose) earlier
          h_composite_earlier ≫ compose =
        pullback.lift later (pullback.lift middle earlier h_middle_earlier ≫ compose)
          h_later_composite ≫ compose := sorry

/-- A completed arrow composed with the identity at its source is unchanged. -/
private theorem completion_right_identity
    (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)) :
    let source := Functor.typesCompletionMap G.s
    let target := Functor.typesCompletionMap G.t
    let identity := Functor.typesCompletionMap G.e
    let compose := (Functor.typesCompletionPullbackIso G.s G.t).inv ≫
      Functor.typesCompletionMap G.c
    ∀ {W : CompleteLocalAlgCat Λ k ⥤ Type w} (arrow : W ⟶ Functor.typesCompletion G.R)
      (h : arrow ≫ source = ((arrow ≫ source) ≫ identity) ≫ target),
      pullback.lift arrow ((arrow ≫ source) ≫ identity) h ≫ compose = arrow := sorry

/-- The identity at a completed arrow's target composed with that arrow is unchanged. -/
private theorem completion_left_identity
    (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)) :
    let source := Functor.typesCompletionMap G.s
    let target := Functor.typesCompletionMap G.t
    let identity := Functor.typesCompletionMap G.e
    let compose := (Functor.typesCompletionPullbackIso G.s G.t).inv ≫
      Functor.typesCompletionMap G.c
    ∀ {W : CompleteLocalAlgCat Λ k ⥤ Type w} (arrow : W ⟶ Functor.typesCompletion G.R)
      (h : ((arrow ≫ target) ≫ identity) ≫ source = arrow ≫ target),
      pullback.lift ((arrow ≫ target) ≫ identity) arrow h ≫ compose = arrow := sorry

/-- A completed arrow composed after its inverse gives the identity at its target. -/
private theorem completion_inverse_comp
    (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)) :
    let source := Functor.typesCompletionMap G.s
    let target := Functor.typesCompletionMap G.t
    let identity := Functor.typesCompletionMap G.e
    let inverse := Functor.typesCompletionMap G.i
    let compose := (Functor.typesCompletionPullbackIso G.s G.t).inv ≫
      Functor.typesCompletionMap G.c
    ∀ {W : CompleteLocalAlgCat Λ k ⥤ Type w} (arrow : W ⟶ Functor.typesCompletion G.R)
      (h : arrow ≫ source = (arrow ≫ inverse) ≫ target),
      pullback.lift arrow (arrow ≫ inverse) h ≫ compose = (arrow ≫ target) ≫ identity := sorry

/-- The inverse of a completed arrow composed after it gives the identity at its source. -/
private theorem completion_comp_inverse
    (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)) :
    let source := Functor.typesCompletionMap G.s
    let target := Functor.typesCompletionMap G.t
    let identity := Functor.typesCompletionMap G.e
    let inverse := Functor.typesCompletionMap G.i
    let compose := (Functor.typesCompletionPullbackIso G.s G.t).inv ≫
      Functor.typesCompletionMap G.c
    ∀ {W : CompleteLocalAlgCat Λ k ⥤ Type w} (arrow : W ⟶ Functor.typesCompletion G.R)
      (h : (arrow ≫ inverse) ≫ source = arrow ≫ target),
      pullback.lift (arrow ≫ inverse) arrow h ≫ compose = (arrow ≫ source) ≫ identity := sorry

/-- The completion of a groupoid in functors on `ArtinianLocalAlgCat Λ k`, obtained by
completing the object and arrow functors and the structure maps, and transporting
composition along `Functor.typesCompletionPullbackIso`. -/
def completion (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)) :
    GroupoidInFunctors.{u + 1, u, w} (CompleteLocalAlgCat Λ k) where
  U := Functor.typesCompletion G.U
  R := Functor.typesCompletion G.R
  s := Functor.typesCompletionMap G.s
  t := Functor.typesCompletionMap G.t
  c := (Functor.typesCompletionPullbackIso G.s G.t).inv ≫ Functor.typesCompletionMap G.c
  e := Functor.typesCompletionMap G.e
  i := Functor.typesCompletionMap G.i
  comp_source := private completion_comp_source G
  comp_target := private completion_comp_target G
  identity_source := private completion_identity_source G
  identity_target := private completion_identity_target G
  inverse_source := private completion_inverse_source G
  inverse_target := private completion_inverse_target G
  associativity := private completion_associativity G
  right_identity := private completion_right_identity G
  left_identity := private completion_left_identity G
  inverse_comp := private completion_inverse_comp G
  comp_inverse := private completion_comp_inverse G

/-- Completion of a groupoid in functors completes the object functor. -/
theorem completion_U (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)) :
    (completion G).U = Functor.typesCompletion G.U := sorry

/-- Completion of a groupoid in functors completes the arrow functor. -/
theorem completion_R (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)) :
    (completion G).R = Functor.typesCompletion G.R := sorry

/-- Completion of a groupoid in functors completes the source map. -/
theorem completion_s (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)) :
    (completion G).s = Functor.typesCompletionMap G.s := sorry

/-- Completion of a groupoid in functors completes the target map. -/
theorem completion_t (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)) :
    (completion G).t = Functor.typesCompletionMap G.t := sorry

/-- Completion of composition is the completed composition, transported by the inverse of
`Functor.typesCompletionPullbackIso`. -/
theorem completion_c (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)) :
    (completion G).c =
      (Functor.typesCompletionPullbackIso G.s G.t).inv ≫ Functor.typesCompletionMap G.c := sorry

/-- Completion of a groupoid in functors completes the identity-arrow map. -/
theorem completion_e (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)) :
    (completion G).e = Functor.typesCompletionMap G.e := sorry

/-- Completion of a groupoid in functors completes the inverse-arrow map. -/
theorem completion_i (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)) :
    (completion G).i = Functor.typesCompletionMap G.i := sorry

/-- The completed groupoid in functors is the source quintuple `(U, R, s, t, c)` together
with the identity and inverse maps, with object and arrow functors completed by
`Functor.typesCompletion` and structure maps completed by `Functor.typesCompletionMap`,
and with composition transported by the inverse of `Functor.typesCompletionPullbackIso`. -/
theorem completion_spec (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)) :
    (completion G).U = Functor.typesCompletion G.U ∧
      (completion G).R = Functor.typesCompletion G.R ∧
      (completion G).s = Functor.typesCompletionMap G.s ∧
      (completion G).t = Functor.typesCompletionMap G.t ∧
      (completion G).c =
        (Functor.typesCompletionPullbackIso G.s G.t).inv ≫
          Functor.typesCompletionMap G.c ∧
      (completion G).e = Functor.typesCompletionMap G.e ∧
      (completion G).i = Functor.typesCompletionMap G.i := sorry

end CategoryTheory.GroupoidInFunctors
